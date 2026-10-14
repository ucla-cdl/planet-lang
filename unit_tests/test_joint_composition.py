"""A joint (multifact) variable is one variable of its leaf design. Composition
blocks it as one variable; its component fields are not design variables of
the composed design, so they are neither analysed nor randomised on their own.
(Rules M-MF and I-MF project the joint's judgments onto its components.)"""
import unittest
import warnings
from collections import Counter
from itertools import product

from planet import Design, ExperimentVariable, Units, assign, cross, multifact, nest
from planet.analysis import Analysis


def variable(name, levels=2):
    return ExperimentVariable(name=name, options=[f"{name}{i}" for i in range(levels)])


def cb(v, trials=None):
    d = Design().within_subjects(v).counterbalance(v)
    return d.num_trials(trials) if trials else d


def between_cb(v):
    return Design().between_subjects(v).counterbalance(v)


def names(effects):
    return {str(v) for v in effects}


def analyse(design):
    with warnings.catch_warnings(record=True) as caught:
        warnings.simplefilter("always")
        analysis = Analysis(design)
    return analysis, any("random variables" in str(w.message) for w in caught)


def project(rows, design, variables):
    """Each cell as the tuple of conditions of the given variables."""
    index = [design.variables.index(v) for v in variables]
    return [[tuple(str(cell).split("-")[i] for i in index) for cell in row] for row in rows]


class JointComposition(unittest.TestCase):
    def setUp(self):
        self.x, self.y, self.g = variable("x"), variable("y"), variable("g")
        self.xy = multifact([self.x, self.y])
        self.sequence = ["x0-y0", "x0-y1", "x1-y0", "x1-y1"]

    def ordered(self):
        return Design().within_subjects(self.xy).order(self.xy, self.sequence)

    def test_components_are_not_design_variables(self):
        z = variable("z", 4)
        cases = [
            (nest(outer=between_cb(self.g), inner=self.ordered()), {"x-y", "g"}, {"x", "y", "g"}),
            (cross(cb(self.xy), cb(z)), {"x-y", "z"}, {"x", "y", "z"}),
            (nest(outer=cb(self.xy), inner=cb(variable("z"))), {"x-y", "z"}, {"x", "y", "z"}),
        ]
        for design, declared, fields in cases:
            with self.subTest(design.composition[0]):
                self.assertEqual(names(design.design_variables), declared)  # the paper's Vars(D)
                self.assertEqual(names(design.variables), fields)           # the bitvector fields

    def test_ordered_joint_components_are_fixed_not_random(self):
        # J2: the order fixes x and y at every position, so neither varies over
        # time; the only time-varying effect is the counterbalanced partner.
        designs = {
            "nest ordered inner": (nest(outer=between_cb(self.g), inner=self.ordered()), {"g"}, "g-x-y"),
            "nest ordered outer": (nest(outer=self.ordered(), inner=cb(variable("w"))), {"w"}, "w-x-y"),
            "cross ordered": (cross(self.ordered(), cb(variable("z", 4))), {"z"}, "x-y-z"),
        }
        for name, (design, time, pair) in designs.items():
            with self.subTest(name):
                analysis, random_warning = analyse(design)
                self.assertFalse(random_warning)
                self.assertEqual(names(analysis.time_varying_effects), time)
                self.assertEqual(names(analysis.main_effects), {"x", "y"} | time)
                self.assertEqual(names(analysis.interaction_effects), {"x-y", pair})

    def test_counterbalanced_joint_keeps_time_effects(self):
        design = nest(outer=between_cb(self.g), inner=cb(self.xy))
        analysis, random_warning = analyse(design)
        self.assertFalse(random_warning)
        self.assertEqual(names(analysis.interaction_effects), {"x-y", "g-x-y"})
        self.assertEqual(names(analysis.time_varying_effects), {"g", "x", "y", "x-y", "g-x-y"})

    def test_random_joint_keeps_random_reports(self):
        designs = {
            "nest within": nest(outer=between_cb(self.g), inner=Design().within_subjects(self.xy)),
            "nest between": nest(outer=between_cb(self.g), inner=Design().between_subjects(self.xy)),
            "cross between": cross(Design().between_subjects(self.xy), between_cb(self.g)),
        }
        for name, design in designs.items():
            with self.subTest(name):
                analysis, random_warning = analyse(design)
                self.assertTrue(random_warning)
                self.assertLessEqual({"x", "y", "x-y"}, names(analysis.time_varying_effects))
                reported = names(analysis.time_varying_effects) | names(analysis.interaction_effects)
                self.assertFalse(reported & {"x-x-y", "x-y-y"})

    def test_repeated_composition_of_a_joint(self):
        # Formerly: ValueError "Cannot add variable 'x' -- it already exists".
        z, w = variable("z"), variable("w")
        inner = nest(outer=cb(self.xy, trials=2).limit_plans(4), inner=cb(z))
        design = nest(outer=inner, inner=cb(w))
        self.assertEqual(design.num_plans(), 4 * 2 * 2)
        self.assertEqual(names(design.design_variables), {"x-y", "z", "w"})
        rows = assign(Units(16), design).computed_plans
        self.assertEqual(len(rows), 16)
        for column in zip(*project(rows, design, [self.x, self.y])):
            self.assertEqual(len(set(Counter(column).values())), 1)

    def test_counterbalanced_joint_survives_each_composition(self):
        # Unequal levels, passed in reverse name order: multifact sorts its components.
        for mode in ("nest_outer", "nest_inner", "cross_first", "cross_second"):
            with self.subTest(mode=mode):
                b, c, z = variable("b", 3), variable("c"), variable("z")
                m = multifact([c, b])
                joint = Design().within_subjects(m).counterbalance(m).num_trials(2).limit_plans(6)
                partner = cb(z) if mode.startswith("nest") else between_cb(z).num_trials(2)
                design = {"nest_outer": lambda: nest(outer=joint, inner=partner),
                          "nest_inner": lambda: nest(outer=partner, inner=joint),
                          "cross_first": lambda: cross(joint, partner),
                          "cross_second": lambda: cross(partner, joint)}[mode]()
                rows = assign(Units(design.num_plans()), design).computed_plans
                self.assertEqual(len(rows), 12)
                expected = set(product(b.conditions, c.conditions))
                for column in zip(*project(rows, design, [b, c])):
                    counts = Counter(column)
                    self.assertEqual(set(counts), {tuple(map(str, p)) for p in expected})
                    self.assertEqual(len(set(counts.values())), 1)

    def test_random_joint_is_drawn_as_one_variable(self):
        # Each inner block of a plan shows every joint condition once: the
        # joint is redrawn as a unit, not x and y separately.
        design = nest(outer=cb(self.g), inner=Design().within_subjects(self.xy))
        rows = assign(Units(4), design).computed_plans
        all_pairs = {(f"x{i}", f"y{j}") for i in range(2) for j in range(2)}
        for row in project(rows, design, [self.x, self.y]):
            for block in (row[:4], row[4:]):
                self.assertEqual(set(block), all_pairs)


if __name__ == "__main__":
    unittest.main()
