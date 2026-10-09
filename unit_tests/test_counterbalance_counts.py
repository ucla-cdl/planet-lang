"""Counterbalancing counts are integers: they must not wrap modulo four.

The finite-semantics tests enumerate every model of a small leaf and compare
it with an independently constructed set of matrices.

Run from the repository root with:

    PYTHONPATH=src python -m unittest discover -s unit_tests -p '*.py' -v
"""
import unittest
from itertools import permutations, product

from z3 import BoolVal, Or, sat, simplify, unsat

from planet import Design, ExperimentVariable
from planet.designer import Designer
from planet.solver import BitVecSolver


def variable(name, levels):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def leaf(var, trials):
    return Design().within_subjects(var).counterbalance(var).num_trials(trials)


def setup(design):
    designer = Designer()
    designer.start(design)
    designer.eval_constraints(
        design.get_constraints(), designer.num_plans, designer.num_trials
    )
    designer.solver.solver.set(timeout=30000)
    return designer


class CounterbalanceCounts(unittest.TestCase):
    def assert_models_match(self, design, expected):
        designer = setup(design)
        solver = designer.solver.solver
        actual = set()
        while True:
            status = solver.check()
            if status == unsat:
                break
            self.assertEqual(status, sat, "enumeration must not time out")
            model = solver.model()
            cells = [model.eval(cell) for cell in designer.solver.z3_variables]
            matrix = tuple(map(tuple, designer.decode(cells).tolist()))
            self.assertNotIn(matrix, actual)
            actual.add(matrix)
            self.assertLessEqual(len(actual), len(expected), "unexpected extra models")
            solver.add(Or([cell != value for cell, value in
                           zip(designer.solver.z3_variables, cells)]))
        self.assertEqual(actual, expected)

    def test_counts_do_not_wrap(self):
        solver = BitVecSolver((1, 1), [variable("a", 2)])
        for count in (0, 3, 4, 5, 8, 17):
            with self.subTest(count=count):
                values = [BoolVal(True)] * count + [BoolVal(False)] * 2
                actual = solver.count(values, None, lambda value, _: value)
                self.assertEqual(simplify(actual).as_long(), count)

    def test_overflow_witness_is_rejected(self):
        a, b = variable("a", 2), variable("b", 4)
        design = (leaf(a, 2).between_subjects(b).counterbalance(b)
                  .limit_plans(4))
        designer = setup(design)
        # Each row is distinct and b is balanced, but a's column counts are
        # (4, 0) and (0, 4), which only agree modulo four.
        designer.solver.name_to_encoding(
            [[f"0-{i}", f"1-{i}"] for i in range(4)]
        )
        self.assertEqual(designer.solver.solver.check(), unsat)

    def test_all_four_row_models_match_exact_balance(self):
        a, b = variable("a", 2), variable("b", 4)
        design = (leaf(a, 2).between_subjects(b).counterbalance(b)
                  .limit_plans(4))

        # Independent finite semantics: b occurs once per column, and exactly
        # two rows start with a=1. There are 6 * 24 = 144 ordered matrices.
        expected = {
            tuple((f"{starts[i]}-{level}", f"{1-starts[i]}-{level}")
                  for i, level in enumerate(levels))
            for starts in product(range(2), repeat=4) if sum(starts) == 2
            for levels in permutations(range(4))
        }
        self.assertEqual(len(expected), 144)
        self.assert_models_match(design, expected)

    def test_partial_within_leaf_matches_finite_semantics(self):
        # Each row uses two different levels, not all three. Column balance
        # still requires every level once in each of the two positions.
        a = variable("a", 3)
        rowspace = list(permutations(("0", "1", "2"), 2))
        expected = {
            rows for rows in permutations(rowspace, 3)
            if all({row[col] for row in rows} == {"0", "1", "2"}
                   for col in range(2))
        }
        self.assertEqual(len(expected), 12)
        self.assert_models_match(leaf(a, 2).limit_plans(3), expected)

    def test_between_leaf_matches_finite_semantics(self):
        a = variable("a", 3)
        design = Design().between_subjects(a).counterbalance(a).num_trials(2)
        expected = set(permutations((("0", "0"), ("1", "1"), ("2", "2"))))
        self.assert_models_match(design, expected)

    def test_fixed_order_leaf_matches_finite_semantics(self):
        a, b = variable("a", 2), variable("b", 2)
        design = leaf(a, 2).within_subjects(b).order(b, ["1", "0"])
        # Reversing the fixed order would produce a different solution set.
        expected = set(permutations((("0-1", "1-0"), ("1-1", "0-0"))))
        self.assert_models_match(design, expected)

    def test_mixed_leaf_matches_finite_semantics(self):
        a, b, c = variable("a", 2), variable("b", 2), variable("c", 2)
        design = (leaf(a, 2).within_subjects(b).counterbalance(b)
                  .between_subjects(c).counterbalance(c).limit_plans(4))
        rowspace = [(f"{a}-{b}-{c}", f"{1-a}-{1-b}-{c}")
                    for a, b, c in product(range(2), repeat=3)]
        expected = {
            rows for rows in permutations(rowspace, 4)
            if all(sum(row[0].split("-")[i] == "1" for row in rows) == 2
                   for i in range(3))
        }
        # Eight balanced four-vertex subsets of the binary cube, each in 4!
        # row orders. This checks joint rows without requiring joint balance.
        self.assertEqual(len(expected), 192)
        self.assert_models_match(design, expected)


if __name__ == "__main__":
    unittest.main()
