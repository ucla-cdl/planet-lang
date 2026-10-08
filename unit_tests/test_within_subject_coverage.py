"""Nested within-subject reports require complete operand conditions."""
import unittest
import warnings

from planet import Design, ExperimentVariable, Units, assign, cross, nest
from planet.analysis import Analysis


def variable(name, levels):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def leaf(var, trials):
    return Design().within_subjects(var).counterbalance(var).num_trials(trials)


class WithinSubjectCoverage(unittest.TestCase):
    def analyse(self, design):
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            return Analysis(design)


    def test_nested_comparisons_require_complete_leaves(self):
        # Test either incomplete side: nesting expands the trial count but
        # cannot supply the missing levels of a four-level, two-trial leaf.
        for outer_levels, inner_levels, expected in (
            (4, 2, {"b"}), (2, 4, {"a"}), (2, 2, {"a", "b", "a-b"})
        ):
            with self.subTest(outer=outer_levels, inner=inner_levels):
                a, b = variable("a", outer_levels), variable("b", inner_levels)
                design = nest(outer=leaf(a, 2), inner=leaf(b, 2))
                comparisons = {str(v) for v in self.analyse(design).ws_comparisons}
                self.assertEqual(comparisons, expected)
                plans = assign(Units(design.num_plans()), design).computed_plans
                self.assertEqual(len(plans), design.num_plans())
                for var in (a, b):
                    index = design.variables.index(var)
                    self.assertTrue(all(
                        len({cell.split("-")[index] for cell in plan}) == 2
                        for plan in plans
                    ))


    def test_cross_is_not_a_within_subjects_interaction(self):
        a, b = variable("a", 2), variable("b", 2)
        design = cross(leaf(a, 2), leaf(b, 2))
        self.assertEqual(
            {str(v) for v in self.analyse(design).ws_comparisons}, {"a", "b"}
        )
