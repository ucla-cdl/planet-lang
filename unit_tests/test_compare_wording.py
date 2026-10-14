"""The analysis names the assumptions an identification rests on, in the paper's words."""
import io
import unittest
import warnings
from contextlib import redirect_stdout

from planet import Design, ExperimentVariable, nest
from planet.analysis import Analysis, compare


def variable(name, *options):
    return ExperimentVariable(name=name, options=list(options))


def counterbalanced(var):
    return Design().within_subjects(var).counterbalance(var)


def compared(design1, design2):
    out = io.StringIO()
    with warnings.catch_warnings(), redirect_stdout(out):
        warnings.simplefilter("ignore", UserWarning)
        compare(design1, design2)
    return out.getvalue()


class CompareWording(unittest.TestCase):
    def setUp(self):
        self.tool = variable("tool", "baseline", "latex")
        self.task = variable("task", "writing", "editing")
        self.d1 = counterbalanced(self.tool)
        self.d2 = (counterbalanced(self.tool).within_subjects(self.task)
                   .counterbalance(self.task).num_trials(2))
        self.d3 = nest(outer=counterbalanced(self.task), inner=counterbalanced(self.tool))

    def test_legend_speaks_of_identification(self):
        out = compared(self.d1, self.d2)
        self.assertIn("+ indicates effects identified in design 1 but not design 2.", out)
        self.assertIn("- indicates effects identified in design 2 but not design 1.", out)
        for old in ("testable", "under assumption", "weaker assumption"):
            self.assertNotIn(old, out)

    def test_shared_main_effect_names_the_assumption_of_the_weaker_design(self):
        # Both designs identify the tool main effect; D1 measures it on one
        # task, so it reads as the effect of tool only without an interaction.
        out = compared(self.d1, self.d2)
        self.assertIn("\t- task\n", out)
        self.assertIn("\t- tool (design 1 identifies it only assuming no interaction with task)\n", out)
        self.assertIn("\t- task-tool\n", out)
        # the other way round, the sign follows the design that can check it
        self.assertIn("\t+ tool (design 2 identifies it only assuming no interaction with task)\n",
                      compared(self.d2, self.d1))

    def test_wider_design_needs_fewer_participants(self):
        out = compared(self.d2, self.d3)
        self.assertIn("\t- task-tool\n", out)
        self.assertIn("Design 2 requires fewer participants than Design 1 to estimate the effect of tool", out)
        self.assertIn("Design 2 requires fewer participants than Design 1 to estimate the effect of task", out)

    def test_fixed_order_interaction_carries_its_assumption(self):
        # task has a fixed order, so its conditions are aliased with position:
        # the tool-task interaction is identified only if tool's effect does
        # not vary over time (rule I-Ord).
        ordered = (counterbalanced(self.tool).within_subjects(self.task)
                   .order(self.task, ["writing", "editing"]).num_trials(2))
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            summary = str(Analysis(ordered))
        self.assertIn("task-tool (assuming no time-varying effect of tool)", summary)
        # compare carries the same label, and the position caveat for the
        # design whose interaction is not separated from position
        out = compared(self.d2, ordered)
        self.assertIn("\t+ task-tool (design 2 identifies it only assuming no time-based effect)\n", out)
        self.assertNotIn("assuming no time-varying effect", compared(self.d1, self.d2))

    def test_main_effect_without_position_balance_names_the_time_assumption(self):
        ordered = Design().within_subjects(self.tool).order(self.tool, ["latex", "baseline"])
        out = compared(self.d1, ordered)
        self.assertIn("\t+ tool (design 2 identifies it only assuming no time-based effect)\n", out)


if __name__ == "__main__":
    unittest.main()
