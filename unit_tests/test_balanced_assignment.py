"""assign(Units(n), d) needs a balanced map: the p plans must divide the n units.

Otherwise it refuses, names the next multiple of p, and leaves the units
unchanged, instead of leaving units unassigned or using a subset of the plans.
"""
import os
import tempfile
import unittest
from collections import Counter
from itertools import permutations

import pandas as pd

from planet import Design, ExperimentVariable, Units, assign
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

    def assert_refused(self, units, design, n, p):
        with self.assertRaisesRegex(
            ValueError, rf"\b{n} \w+ to {p} plans\b.*\bUse {-(-n // p) * p} "
        ):
            assign(units, design)

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

    def test_fixed_design(self):
        design = Design().within_subjects(self.a).counterbalance(self.a)
        for n in (5, 7):
            with self.subTest(n=n):
                self.assert_refused(Units(n), design, n, 6)
        for n in (12, 18):
            with self.subTest(n=n):
                assignment = assign(Units(n), design)
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
                self.assert_refused(Units(n), design, n, 6)
        for n in (12, 18):
            with self.subTest(n=n):
                assignment = assign(Units(n), design)
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

    def test_zero_units_are_balanced(self):
        design = Design().within_subjects(self.a).counterbalance(self.a)
        assignment = assign(Units(0), design)
        self.assertEqual(len(assignment.format_assignment()), 0)

    def test_refusal_keeps_earlier_assignment(self):
        units = Units(12)
        first = assign(units, Design().within_subjects(self.a).counterbalance(self.a))
        before = first.format_assignment()

        c = variable("c", 5)
        five_plans = Design().within_subjects(c).counterbalance(c).limit_plans(5)
        self.assert_refused(units, five_plans, 12, 5)

        pd.testing.assert_frame_equal(first.format_assignment(), before)
        self.assert_balanced(first, 12)

    def test_clusters_count_clusters_not_subunits(self):
        b2, b3 = variable("b", 2), variable("d", 3)
        clusters = Clusters(Units(6), 3)
        self.assert_refused(
            clusters, Design().between_subjects(b2).counterbalance(b2), 3, 2
        )

        # the refused call left the clusters unevaluated, so they assign normally
        assignment = assign(clusters, Design().between_subjects(b3).counterbalance(b3))
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
