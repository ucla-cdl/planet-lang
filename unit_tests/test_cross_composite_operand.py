"""Crossing keeps the plans of a nested or crossed second operand: the plan
matrices of cross(a, b) are the pairings of a matrix of a with a matrix of b,
whichever operand is composite.

Run from the repository root with:

    PYTHONPATH=src python -m unittest discover -s unit_tests -p '*.py' -v
"""
import unittest

from z3 import If, Or, Sum, sat, unsat

from planet import Design, ExperimentVariable, cross, nest
from planet.designer import Designer


def variable(name, levels):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def setup(design):
    designer = Designer()
    designer.start(design)
    designer.eval_constraints(
        design.get_constraints(), designer.num_plans, designer.num_trials
    )
    designer.solver.solver.set(timeout=30000)
    return designer


def matrices(design):
    """Every plan matrix the constraints admit, a cell as (name, level) pairs."""
    designer = setup(design)
    solver = designer.solver.solver
    plans, trials = designer.shape
    read = designer.solver.bitvectors.get_variable_assignment
    cells = designer.solver.z3_variables
    grid = [
        [[(var.name, read(var, cells[r * trials + c])) for var in designer.variables]
         for c in range(trials)]
        for r in range(plans)
    ]
    found = set()
    while (status := solver.check()) == sat:
        model = solver.model()
        value = lambda field: model.evaluate(field, model_completion=True)
        found.add(tuple(
            tuple(tuple(sorted((name, value(field).as_long()) for name, field in cell))
                  for cell in row)
            for row in grid
        ))
        solver.add(Or([
            field != value(field) for row in grid for cell in row for _, field in cell
        ]))
    assert status == unsat
    return found


def crossed(first, second):
    """Row i2 * p1 + i1 pairs plan i1 of the first with plan i2 of the second."""
    return tuple(
        tuple(tuple(sorted(a + b)) for a, b in zip(row1, row2))
        for row2 in second for row1 in first
    )


def nested(outer, inner):
    """Each outer cell holds a whole inner plan."""
    return tuple(
        tuple(tuple(sorted(o + i)) for o in row_o for i in row_i)
        for row_o in outer for row_i in inner
    )


def build(tree):
    """Return the design of a tree and the matrices its operands compose to."""
    kind, *parts = tree
    if kind == "leaf":
        return parts[0](), matrices(parts[0]())
    (design1, matrices1), (design2, matrices2) = build(parts[0]), build(parts[1])
    if kind == "cross":
        return cross(design1, design2), {
            crossed(a, b) for a in matrices1 for b in matrices2
        }
    return nest(outer=design1, inner=design2), {
        nested(o, i) for o in matrices1 for i in matrices2
    }


def balanced(var):
    return lambda: Design().within_subjects(var).counterbalance(var)


def fixed(var):
    return lambda: Design().within_subjects(var).order(
        var, [str(i) for i in range(len(var))]
    )


def groups(var, balance=True):
    def make():
        design = Design().between_subjects(var)
        return design.counterbalance(var) if balance else design
    return make


class CrossWithCompositeOperand(unittest.TestCase):
    def test_plan_matrices_are_the_pairings_of_the_operands(self):
        x, y, z = variable("x", 2), variable("y", 2), variable("z", 2)
        g, s = variable("g", 3), variable("s", 2)
        leaf = lambda make: ("leaf", make)
        nest_yz = ("nest", leaf(balanced(y)), leaf(groups(z, balance=False)))
        cross_yz = ("cross", leaf(balanced(y)), leaf(balanced(z)))
        nest_gs = ("nest", leaf(groups(g)), leaf(fixed(s)))
        trees = {
            "fixed order with a nest": ("cross", leaf(fixed(x)), nest_yz),
            "a nest with a fixed order": ("cross", nest_yz, leaf(fixed(x))),
            "fixed order with a cross": ("cross", leaf(fixed(x)), cross_yz),
            "a cross with a fixed order": ("cross", cross_yz, leaf(fixed(x))),
            "two plans with a nest of three": ("cross", leaf(balanced(x)), nest_gs),
            "a nest of three with two plans": ("cross", nest_gs, leaf(balanced(x))),
            "a nest with a cross": ("cross", nest_gs, ("cross", leaf(balanced(x)), leaf(fixed(y)))),
        }
        for name, tree in trees.items():
            with self.subTest(name):
                design, expected = build(tree)
                self.assertTrue(expected)
                self.assertEqual(matrices(design), expected)

    def test_counterbalance_covers_every_plan_of_the_second_operand(self):
        # v is counterbalanced over four plans that w keeps distinct, so
        # balancing v over only some of them leaves it free on the others.
        x, v, w, s = variable("x", 2), variable("v", 2), variable("w", 3), variable("s", 2)
        outer = (
            Design().between_subjects(v).counterbalance(v)
            .between_subjects(w).limit_plans(4)
        )
        design = cross(balanced(x)(), nest(outer=outer, inner=fixed(s)()))
        designer = setup(design)
        solver = designer.solver.solver
        self.assertEqual(solver.check(), sat)
        plans, trials = designer.shape
        read = designer.solver.bitvectors.get_variable_assignment
        first_trial = designer.solver.z3_variables[::trials]
        solver.add(Sum([If(read(v, cell) == 0, 1, 0) for cell in first_trial]) != plans // 2)
        self.assertEqual(solver.check(), unsat)


if __name__ == "__main__":
    unittest.main()
