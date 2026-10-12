"""assign(Units(n), d) gives every unit one of the p plans.

When p divides n every plan gets the same number of units. Otherwise the
counts differ by at most one, no unit is left unassigned, and a warning says
how the units fall and names the nearest number of units that p divides.
"""
import os
import tempfile
import unittest
import warnings
from collections import Counter
from itertools import permutations

import pandas as pd

from planet import Design, ExperimentVariable, Units, assign
from planet.assignment import allocation_warning
from planet.unit import Clusters


def variable(name, levels):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def realized(assignment, name):
    """Each unit's sequence of `name` conditions, read through its plan index."""
    index = [v.name for v in assignment.plans.variables].index(name)
    rows = assignment.computed_plans
    units = assignment.format_assignment()
    for plan in units.plan:
        assert 0 <= plan < len(rows), f"unit plan {plan} is not a row"
    return [
        tuple(cell.split("-")[index] for cell in rows[plan])
        for plan in units.plan
    ]


def csv_pids(assignment):
    cwd = os.getcwd()
    with tempfile.TemporaryDirectory() as tmp:
        os.chdir(tmp)
        try:
            assignment.to_csv()
            return list(pd.read_csv(os.path.join("outputs", "assignment.csv")).pid)
        finally:
            os.chdir(cwd)


class BalancedAssignment(unittest.TestCase):
    def setUp(self):
        self.a = variable("a", 3)
        # full counterbalancing of 3 conditions: 3! = 6 plans
        self.a_orders = set(permutations("012"))

    def assign_warned(self, units, design, *fragments):
        """Assign, and check that one warning was given containing `fragments`."""
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            assignment = assign(units, design)
        messages = [str(w.message) for w in caught if "Assigning" in str(w.message)]
        self.assertEqual(len(messages), 1, messages)
        for fragment in fragments:
            self.assertIn(fragment, messages[0])
        return assignment

    def assign_silent(self, units, design):
        with warnings.catch_warnings(record=True) as caught:
            warnings.simplefilter("always")
            assignment = assign(units, design)
        self.assertEqual([str(w.message) for w in caught if "Assigning" in str(w.message)], [])
        return assignment

    def assert_balanced(self, assignment, n):
        """Every unit is assigned, exported, and a is counterbalanced over them."""
        sequences = realized(assignment, "a")
        self.assertEqual(len(sequences), n)
        for position in range(3):
            self.assertEqual(
                Counter(sequence[position] for sequence in sequences),
                {condition: n // 3 for condition in "012"},
            )
        self.assertEqual(sorted(csv_pids(assignment)), list(range(1, n + 1)))

    def test_warning_text(self):
        self.assertIsNone(allocation_warning(6, 3))
        self.assertIsNone(allocation_warning(0, 3))
        self.assertEqual(
            allocation_warning(2, 3),
            "Assigning 2 units to 3 plans: 1 plan is not used, so the properties of "
            "the design do not hold over these units. Use at least 3 units, one for each plan.",
        )
        self.assertEqual(
            allocation_warning(5, 3),
            "Assigning 5 units to 3 plans: 2 plans receive 2 units and 1 plan receives "
            "1 unit, so the properties of the design do not hold exactly over these units. "
            "Use 6 units (1 more) to give every plan the same number.",
        )
        self.assertEqual(
            allocation_warning(7, 3),
            "Assigning 7 units to 3 plans: 1 plan receives 3 units and 2 plans receive "
            "2 units, so the properties of the design do not hold exactly over these units. "
            "Use 6 units (1 fewer) to give every plan the same number.",
        )
        # equally near to 4 and to 8: the larger is named
        self.assertIn("Use 8 units (2 more)", allocation_warning(6, 4))
        self.assertIn("3 clusters to 2 plans", allocation_warning(3, 2, "clusters"))

    def test_fixed_design(self):
        design = Design().within_subjects(self.a).counterbalance(self.a)
        for n, advice in ((5, "Use at least 6 units"), (7, "Use 6 units (1 fewer)"), (10, "Use 12 units (2 more)")):
            with self.subTest(n=n):
                assignment = self.assign_warned(Units(n), design, f"{n} unit", "6 plans", advice)
                plans = list(assignment.format_assignment().plan)
                # every unit has a plan, and the plans are used as evenly as possible
                self.assertEqual(len(plans), n)
                self.assertTrue(all(0 <= plan < 6 for plan in plans))
                counts = [plans.count(plan) for plan in range(6)]
                self.assertLessEqual(max(counts) - min(counts), 1)
                self.assertEqual(sorted(csv_pids(assignment)), list(range(1, n + 1)))
        for n in (12, 18):
            with self.subTest(n=n):
                assignment = self.assign_silent(Units(n), design)
                self.assert_balanced(assignment, n)
                self.assertEqual(len(assignment.computed_plans), 6)
                self.assertEqual(
                    Counter(realized(assignment, "a")),
                    {order: n // 6 for order in self.a_orders},
                )

    def test_design_with_random_factor(self):
        g = variable("g", 2)
        design = (
            Design()
            .within_subjects(self.a)
            .counterbalance(self.a)
            .between_subjects(g)
        )
        for n in (5, 7):
            with self.subTest(n=n):
                assignment = self.assign_warned(Units(n), design, f"{n} units to")
                table = assignment.format_assignment()
                rows = assignment.computed_plans
                # every unit follows a row of its own
                self.assertEqual(len(set(table.plan)), n)
                self.assertTrue(all(0 <= plan < len(rows) for plan in table.plan))
                # and the solver plans behind those rows are used as evenly as possible
                copies = -(-n // self.solver_plans(design))
                used = Counter(plan // copies for plan in table.plan)
                counts = [used[plan] for plan in range(self.solver_plans(design))]
                self.assertLessEqual(max(counts) - min(counts), 1)
        for n in (12, 18):
            with self.subTest(n=n):
                assignment = self.assign_silent(Units(n), design)
                # Solver rows are distinct as (a, g) rows, so a may repeat
                # three cyclic orders instead of using all six permutations.
                self.assert_balanced(assignment, n)
                # every unit follows its own expanded row, with its own random draw
                self.assertEqual(
                    sorted(assignment.format_assignment().plan), list(range(n))
                )
                g_cells = {
                    cell for sequence in realized(assignment, "g") for cell in sequence
                }
                self.assertLessEqual(g_cells, {"0", "1"})

    @staticmethod
    def solver_plans(design):
        from planet.plans import PlanGenerator
        generator = PlanGenerator(design, 1)
        generator.generate()
        return generator.num_plans

    def test_zero_units_are_balanced(self):
        design = Design().within_subjects(self.a).counterbalance(self.a)
        assignment = self.assign_silent(Units(0), design)
        self.assertEqual(len(assignment.format_assignment()), 0)

    def test_no_unit_is_left_unassigned(self):
        # 16 units on 25 plans, as in the ARTiST program of the evaluation
        c = variable("c", 5)
        s = variable("s", 5)
        from planet import cross
        design = cross(
            Design().within_subjects(c).counterbalance(c).limit_plans(5),
            Design().within_subjects(s).counterbalance(s).limit_plans(5),
        )
        assignment = self.assign_warned(
            Units(16), design, "16 units to 25 plans", "9 plans are not used", "Use at least 25 units"
        )
        plans = list(assignment.format_assignment().plan)
        self.assertEqual(len(set(plans)), 16)
        self.assertNotIn(-1, plans)

    def test_strict_refuses_and_keeps_earlier_assignment(self):
        units = Units(12)
        first = assign(units, Design().within_subjects(self.a).counterbalance(self.a), strict=True)
        before = first.format_assignment()

        c = variable("c", 5)
        five_plans = Design().within_subjects(c).counterbalance(c).limit_plans(5)
        with self.assertRaisesRegex(ValueError, r"12 units to 5 plans.*Use 10 units \(2 fewer\)"):
            assign(units, five_plans, strict=True)

        pd.testing.assert_frame_equal(first.format_assignment(), before)
        self.assert_balanced(first, 12)

    def test_clusters_count_clusters_not_subunits(self):
        b2, b3 = variable("b", 2), variable("d", 3)
        clusters = Clusters(Units(6), 3)
        assignment = self.assign_warned(
            clusters, Design().between_subjects(b2).counterbalance(b2),
            "3 clusters to 2 plans", "Use 4 clusters (1 more)",
        )
        table = assignment.format_assignment()
        self.assertEqual(sorted(Counter(table.plan).values()), [1, 2])
        for cluster, plan in zip(table.pid, table.plan):
            for unit in clusters.get_units(cluster):
                self.assertEqual(clusters.units.get_plan(unit), plan)

        clusters = Clusters(Units(6), 3)
        assignment = self.assign_silent(clusters, Design().between_subjects(b3).counterbalance(b3))
        table = assignment.format_assignment()
        self.assertEqual(sorted(table.plan), [0, 1, 2])
        subunit_plans = Counter()
        for cluster, plan in zip(table.pid, table.plan):
            for unit in clusters.get_units(cluster):
                self.assertEqual(clusters.units.get_plan(unit), plan)
                subunit_plans[plan] += 1
        self.assertEqual(subunit_plans, {0: 2, 1: 2, 2: 2})


if __name__ == "__main__":
    unittest.main()
