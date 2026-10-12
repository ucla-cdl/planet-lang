"""Regression tests: the nested-pair analysis must not crash on ordered variables.

Two checks in `Analysis.analyze_interaction_effects` multiplied a block
constraint by an integer (`outer_spec * outer_spec.stride`), so any nested
pair with an ordered variable whose no-repeat window was narrower than its
block raised `TypeError`. Those checks could never be true, so dropping them
changes no analysis that previously completed.
"""
import unittest
import warnings

from planet import Design, ExperimentVariable, Units, assign, nest
from planet.analysis import Analysis


def variable(name, levels=2):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def effects(analysis):
    return {frozenset(str(v) for v in pair.get_variables())
            for pair in analysis.interaction_effects}


class NestedAnalysis(unittest.TestCase):
    def analyse(self, design):
        def snapshot():
            # constraint attributes by value; variables by name
            render = lambda v: [str(x) for x in v] if isinstance(v, list) else v
            return [(str(c.variable), {k: render(v) for k, v in vars(c).items() if k != 'variable'})
                    for c in design.get_constraints()]
        before = snapshot()
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', UserWarning)
            result = Analysis(design)
        after = snapshot()
        self.assertEqual(before, after, "analysis must not change the constraints")
        return result

    def test_ordered_outer_leaf_over_nested_counterbalanced_leaves(self):
        # Raised `TypeError: unsupported operand type(s) for *: 'int' and 'InnerBlock'`.
        # No leaf has more trials than conditions; the rules of the paper derive
        # every pairwise interaction (I-Ord for a with b and c, I-Nest for b with c).
        a, b, c = variable('a'), variable('b'), variable('c')
        cb = lambda v: Design().within_subjects(v).counterbalance(v)
        design = nest(outer=Design().within_subjects(a).order(a, ['1', '0']),
                      inner=nest(outer=cb(b), inner=cb(c)))
        result = self.analyse(design)
        self.assertEqual({str(v) for v in result.main_effects}, {'a', 'b', 'c'})
        self.assertEqual(effects(result), {frozenset(('a', 'b')), frozenset(('a', 'c')), frozenset(('b', 'c'))})
        self.assertEqual({str(v) for v in result.time_varying_effects}, {'b', 'c', 'b-c'})

    def test_ordered_inner_leaf_under_counterbalanced_outer(self):
        # Raised `TypeError: unsupported operand type(s) for *: 'int' and 'OuterBlock'`.
        b, x = variable('b'), variable('x')
        inner = Design().within_subjects(x).order(x, ['0', '1']).num_trials(3)
        design = nest(outer=Design().within_subjects(b).counterbalance(b), inner=inner)
        result = self.analyse(design)
        self.assertIn('b', {str(v) for v in result.main_effects})

    def test_depth_two_nest_with_ordered_outer(self):
        # Raised `TypeError: unsupported operand type(s) for *: 'int' and 'InnerBlock'`
        # although no leaf has more trials than conditions and assign returns plans.
        a, b, c = variable('a', 3), variable('b', 3), variable('c', 3)
        design = nest(
            outer=Design().within_subjects(a).order(a, ['1', '2', '0']),
            inner=nest(outer=Design().within_subjects(b).counterbalance(b).num_trials(2),
                       inner=Design().within_subjects(c).start_with(c, '1')))
        result = self.analyse(design)
        self.assertEqual(design.num_plans(), 12)
        self.assertIn(frozenset(('a', 'b')), effects(result))
        self.assertEqual(len(assign(Units(12), design).computed_plans), 12)


if __name__ == '__main__':
    unittest.main()
