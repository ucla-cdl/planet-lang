"""limit_plans on a nest or a cross limits one side and rebuilds the composition."""
import unittest
import warnings
from itertools import permutations

from planet import Design, ExperimentVariable, Units, assign, cross, nest
from planet.analysis import Analysis
from planet.designer import Designer


def variable(name, levels):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def counterbalanced(var):
    return Design().within_subjects(var).counterbalance(var)


def matrix(design):
    designer = Designer()
    designer.start(design)
    return [[str(cell) for cell in row] for row in designer.eval()]


def field(design, var, cell):
    """The value of `var` in a cell string, which lists the fields of the design."""
    return cell.split("-")[design.variables.index(var)]


def latin_square(rows):
    """Each row a permutation of the same symbols, each symbol once per column."""
    symbols = set(rows[0])
    return (all(set(row) == symbols and len(row) == len(symbols) for row in rows)
            and all(set(column) == symbols for column in zip(*rows)))


class LimitComposition(unittest.TestCase):
    def analyse(self, design):
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            return Analysis(design)

    def effects(self, design):
        analysis = self.analyse(design)
        return tuple({str(v) for v in effects} for effects in
                     (analysis.main_effects, analysis.interaction_effects,
                      analysis.ws_comparisons))

    def test_nest_limit_passes_to_the_outer_design(self):
        # 6 orders of a over 2 orders of b: 12 plans of 6 trials. A limit of
        # six keeps both orders of b and gives a a Latin square.
        a, b = variable("a", 3), variable("b", 2)
        design = nest(outer=counterbalanced(a), inner=counterbalanced(b)).limit_plans(6)
        self.assertEqual(design.num_plans(), 6)
        kind, outer, inner = design.composition
        self.assertEqual((kind, outer.num_plans(), inner.num_plans()), ("nest", 3, 2))
        self.assertEqual(design.composition_relation(a, b), "nest")

        rows = matrix(design)
        self.assertEqual((len(rows), len(rows[0])), (6, 6))
        a_of = [[field(design, a, cell) for cell in row] for row in rows]
        b_of = [[field(design, b, cell) for cell in row] for row in rows]
        # a is constant over each block of two trials and two plans, and
        # its three block sequences form a Latin square
        for i in range(0, 6, 2):
            self.assertEqual(a_of[i], a_of[i + 1])
            self.assertEqual(a_of[i][::2], a_of[i][1::2])
        self.assertTrue(latin_square([a_of[i][::2] for i in range(0, 6, 2)]))
        # b takes both of its orders in every block
        for start in range(0, 6, 2):
            self.assertEqual({tuple(row[start:start + 2]) for row in b_of},
                             {("0", "1"), ("1", "0")})
        # the analysis of the limited design is that of a nest
        main, inter, within = self.effects(design)
        self.assertEqual((main, inter, within), ({"a", "b"}, {"a-b"}, {"a", "b", "a-b"}))

    def test_cross_limit_passes_to_the_second_design(self):
        # 6 orders of a crossed with 6 orders of c: 36 plans. A limit of 18
        # keeps every order of a and gives c a Latin square.
        a, c = variable("a", 3), variable("c", 3)
        design = cross(counterbalanced(a), counterbalanced(c)).limit_plans(18)
        self.assertEqual(design.num_plans(), 18)
        kind, first, second = design.composition
        self.assertEqual((kind, first.num_plans(), second.num_plans()), ("cross", 6, 3))

        rows = matrix(design)
        self.assertEqual((len(rows), len(rows[0])), (18, 3))
        a_of = [tuple(field(design, a, cell) for cell in row) for row in rows]
        c_of = [tuple(field(design, c, cell) for cell in row) for row in rows]
        self.assertTrue(latin_square(sorted(set(c_of))))
        for start in range(0, 18, 6):
            self.assertEqual(set(a_of[start:start + 6]), set(permutations(("0", "1", "2"))))
            self.assertEqual(len(set(c_of[start:start + 6])), 1)
        self.assertEqual(self.effects(design)[1], {"a-c"})

    def test_limit_rounds_down_and_never_adds_plans(self):
        a, b = variable("a", 3), variable("b", 2)
        for limit, plans in ((6, 6), (7, 6), (8, 6), (11, 6), (12, 12), (18, 12)):
            with self.subTest(limit=limit):
                design = nest(outer=counterbalanced(a), inner=counterbalanced(b))
                self.assertEqual(design.limit_plans(limit).num_plans(), plans)
        # A second limit on the composition cannot give it plans back.
        design = nest(outer=counterbalanced(a), inner=counterbalanced(b))
        self.assertEqual(design.limit_plans(6).limit_plans(12).num_plans(), 6)
        # A limit stated on a leaf is respected by a limit on the composition.
        design = nest(outer=counterbalanced(a).limit_plans(3), inner=counterbalanced(b))
        self.assertEqual(design.num_plans(), 6)
        self.assertEqual(design.limit_plans(12).num_plans(), 6)

    def test_limit_below_the_step_is_refused(self):
        a, b, c, d = variable("a", 3), variable("b", 2), variable("c", 3), variable("d", 3)
        cases = {
            "nest": (nest(outer=counterbalanced(a), inner=counterbalanced(b)), 5, 6),
            "cross": (cross(counterbalanced(a), counterbalanced(c)), 15, 18),
            "cross of a cross": (cross(counterbalanced(a), cross(counterbalanced(c), counterbalanced(d))), 54, 108),
            "random outer": (nest(outer=Design().between_subjects(d),
                                  inner=counterbalanced(b).within_subjects(variable("e", 2))
                                  .counterbalance(variable("e", 2))), 2, 4),
        }
        for name, (design, limit, step) in cases.items():
            with self.subTest(name):
                plans = design.num_plans()
                with self.assertRaises(ValueError) as refused:
                    design.limit_plans(limit)
                self.assertIn(f"multiples of {step}", str(refused.exception))
                # the design is unchanged
                self.assertEqual(design.num_plans(), plans)

    def test_deep_compositions_limit_one_leaf(self):
        a, b, c, d = variable("a", 3), variable("b", 2), variable("c", 3), variable("d", 3)
        design = cross(counterbalanced(a), cross(counterbalanced(c), counterbalanced(d)))
        self.assertEqual(design.num_plans(), 216)
        self.assertEqual(design.limit_plans(108).num_plans(), 108)
        _, first, second = design.composition
        _, c_side, d_side = second.composition
        self.assertEqual((first.num_plans(), c_side.num_plans(), d_side.num_plans()), (6, 6, 3))
        self.assertEqual(self.effects(design)[1], {"a-c", "a-d", "c-d"})

        design = nest(outer=nest(outer=counterbalanced(a), inner=counterbalanced(b)),
                      inner=counterbalanced(c))
        self.assertEqual(design.num_plans(), 72)
        self.assertEqual(design.limit_plans(36).num_plans(), 36)
        _, outer, c_side = design.composition
        _, a_side, b_side = outer.composition
        self.assertEqual((a_side.num_plans(), b_side.num_plans(), c_side.num_plans()), (3, 2, 6))
        self.assertEqual(design.composition_relation(a, c), "nest")
        self.assertEqual(design.composition_relation(a, b), "nest")

    def test_the_sides_are_not_modified(self):
        a, b = variable("a", 3), variable("b", 2)
        outer, inner = counterbalanced(a), counterbalanced(b)
        design = nest(outer=outer, inner=inner).limit_plans(6)
        self.assertEqual((outer.num_plans(), inner.num_plans()), (6, 2))
        self.assertEqual(design.composition[1].num_plans(), 3)
        # and the trial count survives the rebuild
        self.assertEqual(design.get_width(), 6)
        self.assertEqual(len(assign(Units(6), design).computed_plans), 6)

    def test_leaf_limit_is_capped_with_a_between_subjects_variable(self):
        # The cap at the default number of plans applies whatever the
        # variables of the leaf. Eighteen plans were asked of a design with
        # six, and generation failed.
        a, b = variable("a", 3), variable("b", 2)
        design = Design().within_subjects(a).counterbalance(a).between_subjects(b)
        self.assertEqual(design.num_plans(), 6)
        self.assertEqual(design.limit_plans(18).num_plans(), 6)
        rows = matrix(design)
        self.assertEqual(len(rows), 6)
        self.assertEqual({tuple(field(design, a, cell) for cell in row) for row in rows},
                         set(permutations(("0", "1", "2"))))
        self.assertEqual(design.limit_plans(3).num_plans(), 3)
        self.assertTrue(latin_square([[field(design, a, cell) for cell in row]
                                      for row in matrix(design)]))

    def test_a_limit_needs_a_plan(self):
        a, b = variable("a", 3), variable("b", 2)
        for design in (counterbalanced(a), Design().between_subjects(b),
                       nest(outer=counterbalanced(a), inner=counterbalanced(b))):
            for limit in (0, -1):
                with self.subTest(design=design.composition, limit=limit):
                    with self.assertRaises(ValueError):
                        design.limit_plans(limit)


if __name__ == "__main__":
    unittest.main()
