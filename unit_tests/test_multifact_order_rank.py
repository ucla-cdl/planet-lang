"""Joint order/rank constraints must describe tuples, not a missing packed field."""
import itertools
import unittest

from z3 import Or, Solver, sat, unsat

from planet import Design, ExperimentVariable, cross, multifact, nest
from planet.designer import Designer
from planet.solver import BitVecSolver


def variable(name, n):
    return ExperimentVariable(name=name, options=[str(i) for i in range(n)])


def compile_design(design):
    designer = Designer()
    designer.start(design)
    designer.eval_constraints(design.get_constraints(), *designer.shape)
    return designer.solver


def joint_rows(design, joint):
    """Enumerate the complete one-plan projection using actual atomic fields."""
    compiled = compile_design(design)
    assert compiled.shape[0] == 1
    fields = [[compiled.bitvectors.get_variable_assignment(v, cell)
               for v in joint.get_variables()] for cell in compiled.z3_variables]
    solver = Solver()
    solver.set(timeout=30000)
    solver.add(compiled.solver.assertions())
    rows = set()
    while (status := solver.check()) == sat:
        model = solver.model()
        values = tuple(tuple(model.eval(f).as_long() for f in cell) for cell in fields)
        rows.add(values)
        solver.add(Or([f != value for cell, vals in zip(fields, values)
                       for f, value in zip(cell, vals)]))
    assert status == unsat, solver.reason_unknown()
    return rows


def allowed_rows(joint, ranks):
    tuples = list(itertools.product(*(range(len(v)) for v in joint.variables)))
    return {tuple(tuples[i] for i in order)
            for order in itertools.permutations(range(len(joint)))
            if all(ranks[a] >= ranks[b] for a, b in zip(order, order[1:]))}


class MultiFactOrderRank(unittest.TestCase):
    def test_scalar_order_and_rank_are_unchanged(self):
        v = variable('v', 4)
        ordered = Design().within_subjects(v).order(v, ['3', '0', '2', '1'])
        self.assertEqual(joint_rows(ordered, v), {((3,), (0,), (2,), (1,))})
        ranked = (Design().within_subjects(v).absolute_rank(v, '0', -1)
                  .absolute_rank(v, '3', 1).limit_plans(1))
        self.assertEqual(joint_rows(ranked, v),
                         {((3,), (1,), (2,), (0,)), ((3,), (2,), (1,), (0,))})

    def test_order_is_the_exact_joint_sequence(self):
        a, b = variable('a', 2), variable('b', 3)
        joint = multifact([b, a])  # Constructor sorts components by name.
        indexes = [5, 0, 3, 1, 4, 2]
        sequence = [joint.conditions[i] for i in indexes]
        design = Design().within_subjects(joint).order(joint, sequence)
        tuples = list(itertools.product(range(2), range(3)))
        self.assertEqual(joint_rows(design, joint), {tuple(tuples[i] for i in indexes)})

    def test_signed_ranks_ties_and_equal_ranks(self):
        for ranks in ([2, 1, 0, -1], [1, 1, -2, -2], [0, 0, 0, 0]):
            with self.subTest(ranks=ranks):
                joint = multifact([variable('a', 2), variable('b', 2)])
                design = Design().within_subjects(joint)
                for condition, rank in zip(joint.conditions, ranks):
                    design.absolute_rank(joint, condition, rank)
                design.limit_plans(1)
                self.assertEqual(joint_rows(design, joint), allowed_rows(joint, ranks))

    def test_single_and_list_start_and_rank_override(self):
        for starts in ([2], [1, 2]):
            with self.subTest(starts=starts):
                joint = multifact([variable('a', 2), variable('b', 2)])
                condition = (joint.conditions[starts[0]] if len(starts) == 1 else
                             [joint.conditions[i] for i in starts])
                design = Design().within_subjects(joint).start_with(joint, condition)
                design.limit_plans(1)
                ranks = [int(i in starts) for i in range(4)]
                self.assertEqual(joint_rows(design, joint), allowed_rows(joint, ranks))
        joint = multifact([variable('a', 2), variable('b', 2)])
        design = (Design().within_subjects(joint).start_with(joint, joint.conditions[0])
                  .absolute_rank(joint, joint.conditions[0], -1).limit_plans(1))
        self.assertEqual(joint_rows(design, joint), allowed_rows(joint, [-1, 0, 0, 0]))

    def test_joint_constraints_survive_composition(self):
        for constraint in ('order', 'rank'):
            for composition in ('nest_outer', 'nest_inner', 'cross_first', 'cross_second'):
                with self.subTest(constraint=constraint, composition=composition):
                    joint = multifact([variable('a', 2), variable('b', 2)])
                    design = Design().within_subjects(joint)
                    if constraint == 'order':
                        indexes = [3, 0, 2, 1]
                        design.order(joint, [joint.conditions[i] for i in indexes])
                        tuples = list(itertools.product(range(2), repeat=2))
                        rows = {tuple(tuples[i] for i in indexes)}
                    else:
                        design.start_with(joint, joint.conditions[:2]).limit_plans(1)
                        rows = allowed_rows(joint, [1, 1, 0, 0])
                    other = Design().between_subjects(variable('z', 1)).num_trials(
                        2 if composition.startswith('nest') else 4)
                    if composition == 'nest_outer':
                        combined = nest(outer=design, inner=other)
                        expected = {tuple(cell for cell in row for _ in range(2)) for row in rows}
                    elif composition == 'nest_inner':
                        combined = nest(outer=other, inner=design)
                        expected = {row * 2 for row in rows}
                    elif composition == 'cross_first':
                        combined, expected = cross(design, other), rows
                    else:
                        combined, expected = cross(other, design), rows
                    self.assertEqual(joint_rows(combined, joint), expected)

    def test_joint_start_contradicts_full_counterbalance(self):
        joint = multifact([variable('a', 2), variable('b', 2)])
        design = (Design().within_subjects(joint).counterbalance(joint)
                  .start_with(joint, joint.conditions[0]).limit_plans(4))
        compiled = compile_design(design)
        solver = Solver()
        solver.set(timeout=30000)
        solver.add(compiled.solver.assertions())
        self.assertEqual(solver.check(), unsat)

    def test_noncontiguous_fields_and_unrelated_variable_are_preserved(self):
        a, middle, b = variable('a', 2), variable('middle', 2), variable('b', 3)
        joint = multifact([b, a])
        # Exercise a valid packed layout without requiring adjacent components.
        compiled = BitVecSolver((1, 6), [a, middle, b])
        indexes = [5, 0, 3, 1, 4, 2]
        compiled.order(joint, indexes, 6, 1)
        solver = Solver()
        solver.add(compiled.solver.assertions())
        read = compiled.bitvectors.get_variable_assignment
        tuples = list(itertools.product(range(2), range(3)))
        for c, index in enumerate(indexes):
            cell = compiled.z3_variables[c]
            av, bv = tuples[index]
            solver.add(read(middle, cell) == c % 2)
            solver.push()
            solver.add(Or(read(a, cell) != av, read(b, cell) != bv))
            self.assertEqual(solver.check(), unsat)
            solver.pop()
        self.assertEqual(solver.check(), sat)


if __name__ == '__main__':
    unittest.main()
