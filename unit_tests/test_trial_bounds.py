"""A leaf design's trials must fit its within-subjects and fixed-order variables."""
import unittest
import warnings

from planet import Design, ExperimentVariable, Units, assign, cross, nest
from planet.analysis import Analysis


def variable(name, levels):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def generate(design):
    return assign(Units(design.num_plans()), design).computed_plans


class TrialBounds(unittest.TestCase):
    def analyse(self, design):
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            return Analysis(design)


    def test_between_subjects_variable_does_not_lift_the_within_bound(self):
        # Three trials of a two-level within-subjects variable: the plans
        # repeated a condition of a when b was beside it.
        a, b = variable("a", 2), variable("b", 2)
        for fix in ("counterbalance", "order"):
            with self.subTest(fix=fix):
                design = Design().within_subjects(a).between_subjects(b).counterbalance(b)
                if fix == "counterbalance":
                    design.counterbalance(a)
                else:
                    design.order(a, ["1", "0"])
                with self.assertRaises(ValueError):
                    generate(design.num_trials(3))
        design = (Design().within_subjects(a).counterbalance(a)
                  .between_subjects(b).counterbalance(b))
        plans = generate(design)
        self.assertEqual(len(plans), 4)
        self.assertTrue(all(len({cell.split("-")[0] for cell in plan}) == 2 for plan in plans))


    def test_fixed_order_needs_one_trial_per_condition(self):
        # A between-subjects variable with one condition repeated it over the
        # trials; two or more conditions stopped with an IndexError.
        for levels, role, trials in ((1, "between", 2), (2, "between", None), (3, "within", 2)):
            with self.subTest(levels=levels, role=role, trials=trials):
                x = variable("x", levels)
                design = getattr(Design(), f"{role}_subjects")(x)
                design.order(x, [str(i) for i in reversed(range(levels))])
                if trials:
                    design.num_trials(trials)
                with self.assertRaisesRegex(ValueError, "order of x"):
                    generate(design)
        x = variable("x", 1)
        self.assertEqual(len(generate(Design().between_subjects(x).order(x, ["0"]))), 1)


    def test_composition_checks_its_leaves(self):
        a, b, x = variable("a", 2), variable("b", 2), variable("x", 2)
        long = lambda: Design().within_subjects(a).counterbalance(a).num_trials(3)
        cb = lambda v: Design().between_subjects(v).counterbalance(v)
        for compose in (lambda: nest(outer=long(), inner=cb(b)),
                        lambda: nest(outer=cb(b), inner=long()),
                        lambda: nest(outer=Design().num_trials(2),
                                     inner=Design().within_subjects(x).order(x, ["1", "0"]).num_trials(3)),
                        lambda: cross(long(), Design().within_subjects(b).counterbalance(b).num_trials(3))):
            with self.assertRaises(ValueError):
                compose()
        # Nesting is how a sequence is repeated.
        design = nest(outer=Design().num_trials(2),
                      inner=Design().within_subjects(x).order(x, ["1", "0"]))
        self.assertEqual([list(plan) for plan in generate(design)], [["1", "0", "1", "0"]])


    def test_one_condition_has_no_time_varying_effect(self):
        # Rule T-CB asks for two or more conditions, as the main effect does.
        c = variable("c", 1)
        for design in (Design().between_subjects(c).counterbalance(c).num_trials(2),
                       Design().within_subjects(c).counterbalance(c)):
            result = self.analyse(design)
            self.assertEqual(result.main_effects, set())
            self.assertEqual(result.time_varying_effects, set())
        a = variable("a", 2)
        result = self.analyse(Design().within_subjects(a).counterbalance(a)
                              .between_subjects(c).counterbalance(c))
        self.assertEqual({str(v) for v in result.time_varying_effects}, {"a"})


if __name__ == '__main__':
    unittest.main()
