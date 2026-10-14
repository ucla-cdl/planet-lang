"""Rule I-Nest: two variables on different sides of a nest, each with a main
effect, have a derivable interaction, whatever their attributes and however
deep the nest. The analysis reads the sides from the composition tree that nest() and cross() record."""
import unittest
import warnings

from planet import Design, ExperimentVariable, nest, cross
from planet.analysis import Analysis


def variable(name, levels=2):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def cb(v):
    return Design().within_subjects(v).counterbalance(v)


def fixed(v):
    return Design().within_subjects(v).order(v, [str(c) for c in reversed(v.conditions)])


def interactions(design):
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', UserWarning)
        analysis = Analysis(design)
    return {frozenset(str(v) for v in pair.get_variables()) for pair in analysis.interaction_effects}


def pairs(*names):
    return {frozenset(p) for p in names}


class NestInteractions(unittest.TestCase):
    def test_two_nested_fixed_orders(self):
        a, b = variable('a'), variable('b')
        self.assertEqual(interactions(nest(outer=fixed(a), inner=fixed(b))), pairs('ab'))

    def test_fixed_orders_of_different_sizes(self):
        a, b = variable('a', 3), variable('b')
        self.assertEqual(interactions(nest(outer=fixed(a), inner=fixed(b))), pairs('ab'))

    def test_depth_two_with_fixed_orders_inside(self):
        a, b, c = variable('a'), variable('b'), variable('c')
        design = nest(outer=cb(a), inner=nest(outer=fixed(b), inner=fixed(c)))
        self.assertEqual(interactions(design), pairs('ab', 'ac', 'bc'))

    def test_depth_two_with_fixed_order_outside(self):
        a, b, c = variable('a'), variable('b'), variable('c')
        design = nest(outer=fixed(a), inner=nest(outer=cb(b), inner=fixed(c)))
        self.assertEqual(interactions(design), pairs('ab', 'ac', 'bc'))

    def test_outermost_and_innermost_pair_under_a_leaf_limit(self):
        # The limit removes the plan-count premise of I-CB; I-Nest still applies
        # to every pair across a nest, including the outermost and innermost.
        a, b, c = variable('a', 3), variable('b', 3), variable('c')
        design = nest(outer=cb(a), inner=nest(outer=cb(b).limit_plans(3), inner=cb(c)))
        self.assertEqual(interactions(design), pairs('ab', 'ac', 'bc'))
        design = nest(outer=cb(a).limit_plans(3), inner=nest(outer=cb(b), inner=cb(c)))
        self.assertEqual(interactions(design), pairs('ab', 'ac', 'bc'))

    def test_cross_is_not_mistaken_for_nest(self):
        # cross(order(a), order(b)) has no interaction by any rule of the paper.
        a, b = variable('a'), variable('b')
        self.assertEqual(interactions(cross(fixed(a), fixed(b))), set())
        # Inside a nest, the crossed pair stays uncounted while the nested ones are.
        c = variable('c')
        design = nest(outer=fixed(c), inner=cross(fixed(a), fixed(b)))
        self.assertEqual(interactions(design), pairs('ac', 'bc'))

    def test_composition_tree_labels(self):
        # The lowest composition that separates two variables labels the pair.
        a, b, c, d = variable('a'), variable('b'), variable('c'), variable('d')
        design = nest(outer=cross(cb(a), cb(b)), inner=nest(outer=cb(c), inner=cb(d)))
        rel = design.composition_relation
        self.assertEqual(rel(a, b), 'cross')
        self.assertEqual(rel(c, d), 'nest')
        for x in (a, b):
            for y in (c, d):
                self.assertEqual(rel(x, y), 'nest')
        leaf = Design().within_subjects(a).counterbalance(a).within_subjects(b)
        self.assertIsNone(leaf.composition_relation(a, b))
        self.assertIsNone(leaf.composition)

    def test_one_condition_variable_has_no_interaction(self):
        a, s = variable('a'), variable('s', 1)
        self.assertEqual(interactions(nest(outer=fixed(a), inner=Design().within_subjects(s))), set())


if __name__ == '__main__':
    unittest.main()
