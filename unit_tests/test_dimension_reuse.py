"""A design can be solved again after its number of trials or plans changes:
default dimensions are resolved against the current design each time.

Run from the repository root with:

    PYTHONPATH=src python -m unittest discover -s unit_tests -p '*.py' -v
"""
import unittest

from z3 import sat, unsat

from planet import Design, ExperimentVariable, Units, assign, cross
from planet.constraint import Counterbalance
from planet.designer import Designer


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


class DimensionReuse(unittest.TestCase):
    def test_regeneration_uses_current_counterbalance_height(self):
        a, b = variable("a", 3), variable("b", 2)
        design = leaf(a, 2).between_subjects(b)
        for height in (3, 6, 3):
            with self.subTest(height=height):
                design.limit_plans(height)
                designer = setup(design)
                plans = designer.decode(designer.solver.get_one_model())
                self.assertEqual(plans.shape, (height, 2))
                self.assertEqual(len(set(map(tuple, plans))), height)
                for row in plans:
                    self.assertEqual(len({cell.split("-")[0] for cell in row}), 2)
                for col in plans.T:
                    levels = [cell.split("-")[0] for cell in col]
                    for level in ("0", "1", "2"):
                        self.assertEqual(levels.count(level), height // 3)
                if height == 6:
                    # The first three rows balance both columns; the added
                    # rows make column zero's counts (3, 2, 1). b keeps all
                    # six rows distinct without forcing a to balance.
                    designer.solver.name_to_encoding([
                        ["0-0", "1-0"], ["1-0", "2-0"], ["2-0", "0-0"],
                        ["0-1", "1-1"], ["0-1", "2-1"], ["1-1", "0-1"],
                    ])
                    self.assertEqual(designer.solver.solver.check(), unsat)

    def test_cross_preserves_partially_explicit_counterbalance_dimensions(self):
        cases = (
            (1, 0, (1, 6), [
                ["0-0", "1-0"], ["1-0", "0-0"], ["2-0", "0-0"],
                ["0-1", "1-1"], ["1-1", "0-1"], ["2-1", "0-1"],
            ]),
            (0, 3, (2, 3), [
                ["0-0", "1-0"], ["1-0", "2-0"], ["2-0", "0-0"],
                ["0-1", "1-1"], ["0-1", "2-1"], ["1-1", "0-1"],
            ]),
        )
        for width, height, expected_dimensions, rows in cases:
            with self.subTest(width=width, height=height):
                a, b, c = variable("a", 3), variable("b", 2), variable("c", 2)
                first = (
                    Design().within_subjects(a)
                    .counterbalance(a, w=width, h=height)
                    .between_subjects(b).num_trials(2).limit_plans(6)
                )
                second = Design().between_subjects(c).counterbalance(c).num_trials(2)
                # These rows satisfy the requested region, but not a region
                # expanded to both columns or all six rows.
                original = setup(first)
                original.solver.name_to_encoding(rows)
                self.assertEqual(original.solver.solver.check(), sat)

                combined = cross(first, second)
                designer = setup(combined)
                designer.solver.name_to_encoding([
                    [f"{cell}-{level}" for cell in row]
                    for level in ("0", "1") for row in rows
                ])
                self.assertEqual(designer.solver.solver.check(), sat)
                copied = next(
                    constraint for constraint in combined.get_constraints()
                    if isinstance(constraint, Counterbalance)
                    and constraint.variable == a
                )
                self.assertEqual((copied.width, copied.height),
                                 expected_dimensions)
                source = next(
                    constraint for constraint in first.get_constraints()
                    if isinstance(constraint, Counterbalance)
                )
                self.assertEqual((source.width, source.height), (width, height))

    def test_regeneration_uses_current_between_subjects_width(self):
        a = variable("a", 3)
        design = Design().between_subjects(a).counterbalance(a)
        for width in (2, 3, 1):
            with self.subTest(width=width):
                design.num_trials(width)
                plans = assign(Units(3), design).computed_plans
                self.assertEqual(plans.shape, (3, width))
                self.assertEqual(set(map(tuple, plans)),
                                 {(level,) * width for level in ("0", "1", "2")})
                if width == 3:
                    # A lucky generated model can look valid even when the
                    # third column is unconstrained. Pin an invalid witness.
                    designer = setup(design)
                    designer.solver.name_to_encoding(
                        [[level, level, "0"] for level in ("0", "1", "2")]
                    )
                    self.assertEqual(designer.solver.solver.check(), unsat)

    def test_random_between_assignment_keeps_trial_span(self):
        a, b = variable("a", 2), variable("b", 3)
        design = leaf(a, 2).between_subjects(b)
        for _ in range(2):
            plans = assign(Units(12), design).computed_plans
            self.assertEqual(len(plans), 12)
            for row in plans:
                self.assertEqual({cell.split("-")[0] for cell in row}, {"0", "1"})
                assigned = {cell.split("-")[1] for cell in row}
                self.assertEqual(len(assigned), 1)
                self.assertTrue(assigned <= {"0", "1", "2"})

    def test_random_between_span_tracks_trial_changes(self):
        a = variable("a", 3)
        design = Design().between_subjects(a)
        for trials in (2, 3, 1, 4):
            design.num_trials(trials)
            plans = assign(Units(6), design).computed_plans
            self.assertEqual(len(plans), 6)
            for row in plans:
                self.assertEqual(len(row), trials)
                self.assertEqual(len(set(row)), 1)
                self.assertTrue(set(row) <= {"0", "1", "2"})


if __name__ == "__main__":
    unittest.main()
