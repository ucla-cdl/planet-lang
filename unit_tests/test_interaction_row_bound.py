"""Counterbalanced interaction reports account for all row-varying factors."""
import unittest
import warnings
from itertools import permutations

from z3 import Or, sat, unsat

from planet import Design, ExperimentVariable, Units, assign, cross, nest
from planet.analysis import Analysis
from planet.constraint import NoRepeat
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


class InteractionRowBound(unittest.TestCase):
    def analyse(self, design):
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", UserWarning)
            return Analysis(design)


    def test_interaction_bound_includes_uncounterbalanced_variables(self):
        # Both between- and within-subjects random variables distinguish rows.
        # Explicit and default plan counts must use the same analysis guard.
        for within, levels, maximum in ((False, 2, 8), (False, 3, 12),
                                         (True, 3, 24)):
            for limit in (0, 4, maximum):
                with self.subTest(within=within, levels=levels, limit=limit):
                    a, b, c = variable("a", 2), variable("b", 2), variable("c", levels)
                    design = leaf(a, 2).within_subjects(b).counterbalance(b)
                    if within:
                        design.within_subjects(c)
                    else:
                        design.between_subjects(c)
                    if limit:
                        design.limit_plans(limit)
                    # A limit is not the actual row count: the within-only
                    # generator still caps this design at four plans.
                    expected_plans = limit if limit and not within else 4
                    self.assertEqual(design._maximum_rows(), maximum)
                    self.assertEqual(design.num_plans(), expected_plans)
                    interactions = {str(v) for v in self.analyse(design).interaction_effects}
                    self.assertEqual("a-b" in interactions, expected_plans == maximum)


    def test_missing_pair_witness_remains_admissible(self):
        a, b, c = variable("a", 2), variable("b", 2), variable("c", 2)
        design = (leaf(a, 2).within_subjects(b).counterbalance(b)
                  .between_subjects(c).limit_plans(4))
        designer = setup(design)
        rows = [["0-0-0", "1-1-0"], ["1-1-0", "0-0-0"],
                ["0-0-1", "1-1-1"], ["1-1-1", "0-0-1"]]
        designer.solver.name_to_encoding(rows)
        self.assertEqual(designer.solver.solver.check(), sat)
        self.assertEqual({cell[:3] for row in rows for cell in row}, {"0-0", "1-1"})
        analysis = self.analyse(design)
        self.assertNotIn("a-b", {str(v) for v in analysis.interaction_effects})
        self.assertNotIn("a-b", {str(v) for v in analysis.time_varying_effects})


    def test_nested_bound_uses_trial_blocks(self):
        for limit, expected in ((6, False), (36, True)):
            with self.subTest(limit=limit):
                a, b, c = variable("a", 3), variable("b", 3), variable("c", 2)
                outer = leaf(a, 3).within_subjects(b).counterbalance(b).limit_plans(limit)
                inner = Design().within_subjects(c).num_trials(2)
                design = nest(outer=outer, inner=inner)
                # Each ternary variable has 3! orders. c repeats the same
                # binary order across all rows, so cannot distinguish them.
                self.assertEqual(design._maximum_rows(), 36)
                self.assertEqual(design.num_plans(), limit)
                analysis = self.analyse(design)
                for effects in (analysis.interaction_effects, analysis.time_varying_effects):
                    self.assertEqual("a-b" in {str(v) for v in effects}, expected)
                if limit == 6:
                    # a and b are perfectly confounded in this admissible
                    # matrix: only the three diagonal pairs ever appear.
                    rows = [
                        [f"{binary}-{level}-{level}"
                         for level in order for binary in (0, 1)]
                        for order in permutations(range(3))
                    ]
                    designer = setup(design)
                    designer.solver.name_to_encoding(rows)
                    self.assertEqual(designer.solver.solver.check(), sat)


    def test_shared_outer_variable_preserves_complete_inner_pair(self):
        pairs = {"0-0", "0-1", "1-0", "1-1"}
        for limit, expected in ((2, False), (4, True)):
            with self.subTest(limit=limit):
                a, b, c = variable("a", 2), variable("b", 2), variable("c", 2)
                inner = leaf(a, 2).within_subjects(b).counterbalance(b).limit_plans(limit)
                outer = Design().between_subjects(c)
                design = nest(outer=outer, inner=inner)
                self.assertEqual(design._maximum_rows(), 4)
                self.assertEqual(design.num_plans(), limit)
                analysis = self.analyse(design)
                for effects in (analysis.interaction_effects, analysis.time_varying_effects):
                    self.assertEqual("a-b" in {str(v) for v in effects}, expected)

                designer = setup(design)
                solver = designer.solver.solver
                if not expected:
                    rows = [["0-0-0", "1-1-0"], ["1-1-0", "0-0-0"]]
                    designer.solver.name_to_encoding(rows)
                    self.assertEqual(solver.check(), sat)
                    continue

                models = 0
                while True:
                    status = solver.check()
                    if status == unsat:
                        break
                    self.assertEqual(status, sat, "enumeration must not time out")
                    model = solver.model()
                    cells = [model.eval(cell) for cell in designer.solver.z3_variables]
                    plans = designer.decode(cells)
                    for col in plans.T:
                        self.assertEqual({"-".join(cell.split("-")[:2]) for cell in col}, pairs)
                    models += 1
                    self.assertLessEqual(models, 48)
                    solver.add(Or([
                        cell != value for cell, value in
                        zip(designer.solver.z3_variables, cells)
                    ]))
                # Two shared c levels, each with all 4! row permutations.
                self.assertEqual(models, 48)


    def test_rank_count_needs_the_no_repeat_window(self):
        # NoRepeat compares trials 0 and 2 while the ranks sort trials 0 and
        # 1, so c has three sequences, 001, 011 and 110, not the two that
        # the ranks leave in a window they share with NoRepeat.
        a, b, c = variable("a", 3), variable("b", 3), variable("c", 2)
        design = (Design().between_subjects(a).counterbalance(a)
                  .between_subjects(b).counterbalance(b))
        design.add_variable(c)
        design.add_constraint(NoRepeat(c, width=3, stride=2))
        design.start_with(c, "0").num_trials(3).limit_plans(18)
        self.assertEqual(design.num_plans(), 18)
        self.assertGreaterEqual(design._maximum_rows(), 27)
        self.assertNotIn("a-b", {str(v) for v in self.analyse(design).interaction_effects})


    def test_oversized_inner_block_does_not_hide_row_variations(self):
        a, b, c = variable("a", 2), variable("b", 2), variable("c", 2)
        inner = leaf(a, 2).within_subjects(b).counterbalance(b)
        design = nest(outer=Design().between_subjects(c), inner=inner).limit_plans(2)
        # c's four-row InnerBlock cannot constrain a two-row matrix. Each
        # of the four a/b orders can have any of four c trial sequences.
        self.assertEqual(design._maximum_rows(), 16)
        designer = setup(design)
        designer.solver.name_to_encoding([
            ["0-0-0", "1-1-1"], ["1-1-1", "0-0-0"],
        ])
        self.assertEqual(designer.solver.solver.check(), sat)
        self.assertNotIn("a-b", {str(v) for v in self.analyse(design).interaction_effects})


    def test_spare_trials_of_fixed_and_ranked_variables_distinguish_rows(self):
        # A between-subjects variable lifts the trial limit, so the third
        # trial of the two-level variable c is outside its sequence.
        for fix in ("order", "start_with"):
            for limit, expected in ((4, False), (8, True)):
                with self.subTest(fix=fix, limit=limit):
                    a, b, c = variable("a", 2), variable("b", 2), variable("c", 2)
                    design = (Design().between_subjects(a).counterbalance(a)
                              .between_subjects(b).counterbalance(b)
                              .within_subjects(c))
                    if fix == "order":
                        design.order(c, ["0", "1"])
                    else:
                        design.start_with(c, "0")
                    design.num_trials(3).limit_plans(limit)
                    self.assertEqual(design._maximum_rows(), 8)
                    self.assertEqual(design.num_plans(), limit)
                    interactions = {str(v) for v in self.analyse(design).interaction_effects}
                    self.assertEqual("a-b" in interactions, expected)
                    if fix == "order" and limit == 4:
                        # Four rows that differ in c's free trial and
                        # contain only two of the four a-b pairs.
                        rows = [["0-0-0", "0-0-1", "0-0-0"], ["0-0-0", "0-0-1", "0-0-1"],
                                ["1-1-0", "1-1-1", "1-1-0"], ["1-1-0", "1-1-1", "1-1-1"]]
                        designer = setup(design)
                        designer.solver.name_to_encoding(rows)
                        self.assertEqual(designer.solver.solver.check(), sat)


    def test_refused_plan_limit_does_not_stop_the_analysis(self):
        # Generation refuses one plan for a counterbalanced binary variable.
        # The analysis ran before and still does, without the implicit pair.
        a = variable("a", 2)
        design = leaf(a, 2).limit_plans(1)
        with self.assertRaises(ValueError):
            design.num_plans()
        analysis = self.analyse(design)
        self.assertEqual({str(v) for v in analysis.main_effects}, {"a"})
        self.assertEqual({str(v) for v in analysis.time_varying_effects}, {"a"})

        a, b = variable("a", 2), variable("b", 2)
        design = leaf(a, 2).within_subjects(b).counterbalance(b).limit_plans(1)
        analysis = self.analyse(design)
        self.assertEqual({str(v) for v in analysis.main_effects}, {"a", "b"})
        self.assertNotIn("a-b", {str(v) for v in analysis.interaction_effects})


    def test_counterbalanced_pair_at_maximum_still_has_interaction(self):
        for limit, expected in ((0, True), (2, False), (4, True)):
            with self.subTest(limit=limit):
                a, b = variable("a", 2), variable("b", 2)
                design = leaf(a, 2).within_subjects(b).counterbalance(b)
                if limit:
                    design.limit_plans(limit)
                self.assertEqual(design._maximum_rows(), 4)
                analysis = self.analyse(design)
                self.assertEqual(
                    "a-b" in {str(v) for v in analysis.interaction_effects}, expected
                )


    def test_random_pair_reports_keep_the_existing_warning_contract(self):
        # This fix targets CB pairs, not the probabilistic reporting contract.
        for mixed in (False, True):
            x, y = variable("x", 2), variable("y", 2)
            design = Design().between_subjects(x).between_subjects(y)
            if mixed:
                design.counterbalance(x)
            with warnings.catch_warnings(record=True) as caught:
                warnings.simplefilter("always")
                analysis = Analysis(design)
            self.assertTrue(any("random variation" in str(w.message) for w in caught))
            self.assertIn("x-y", {str(v) for v in analysis.interaction_effects})
