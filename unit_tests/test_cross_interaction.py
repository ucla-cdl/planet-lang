"""The cross rule reports variables on opposite sides of a cross, not two
variables on the same side.

Run from the repository root with:

    PYTHONPATH=src python -m unittest discover -s unit_tests -p '*.py' -v
"""
import unittest
import warnings

from z3 import sat

from planet import Design, ExperimentVariable, cross
from planet.analysis import Analysis
from planet.designer import Designer


def variable(name, levels=2):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def leaf(*variables):
    design = Design().num_trials(2)
    for var in variables:
        design.within_subjects(var).counterbalance(var)
    return design


def interactions(design):
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", UserWarning)
        return {str(v) for v in Analysis(design).interaction_effects}


class CrossInteraction(unittest.TestCase):
    def test_same_side_pair_keeps_the_plan_guard(self):
        # Two plans of a and b can hold two of their four pairs, and crossing
        # with c repeats those plans. Four plans hold all four.
        for limit, expected in ((2, False), (4, True)):
            for a_b_first in (True, False):
                with self.subTest(limit=limit, a_b_first=a_b_first):
                    a, b, c = variable("a"), variable("b"), variable("c")
                    side, other = leaf(a, b).limit_plans(limit), leaf(c)
                    design = cross(side, other) if a_b_first else cross(other, side)
                    reported = interactions(design)
                    self.assertEqual("a-b" in reported, expected)
                    self.assertLessEqual({"a-c", "b-c"}, reported)

        a, b, c = variable("a"), variable("b"), variable("c")
        design = cross(leaf(a, b).limit_plans(2), leaf(c))
        rows = [["0-1-0", "1-0-1"], ["1-0-0", "0-1-1"],
                ["0-1-1", "1-0-0"], ["1-0-1", "0-1-0"]]
        designer = Designer()
        designer.start(design)
        designer.eval_constraints(
            design.get_constraints(), designer.num_plans, designer.num_trials
        )
        designer.solver.name_to_encoding(rows)
        self.assertEqual(designer.solver.solver.check(), sat)
        self.assertEqual({cell[:3] for row in rows for cell in row}, {"0-1", "1-0"})

    def test_every_pair_across_nested_crosses_is_reported(self):
        a, b, c = variable("a"), variable("b"), variable("c")
        for design in (cross(cross(leaf(a), leaf(b)), leaf(c)),
                       cross(leaf(a), cross(leaf(b), leaf(c)))):
            self.assertEqual(interactions(design), {"a-b", "a-c", "b-c"})


if __name__ == "__main__":
    unittest.main()
