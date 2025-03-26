import sys
sys.path.append("../src")

from z3 import *
from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest, cross
from lib.unit import Units, Clusters
from lib.assignment import assign
from lib.solver import BitVecSolver
import numpy as np
import unittest
import duckdb


def is_unique(col):
    arr = col.to_numpy() 
    return (arr[0] == arr).all()

class TestSolver(unittest.TestCase):
    def test_counterbalanced_assignment(self):
        count = ExperimentVariable(
            name = "count",
            options = ["1", "2", "3"]
        )
        units = Units(27)

        des = (
            Design()
                .within_subjects(count)
                .counterbalance(count)
                .limit_groups(len(count))
        )


        assignment = assign(units, des)
        df = duckdb.sql(f"select count(pid) from {assignment.units.table} group by plan").df()
        assert is_unique(df["count(pid)"])

    def test_cluster(self):
        treatment = ExperimentVariable(
            name = "treatment",
            options = ["a", "b", "c"]
        )

        units = Units(24)

        clusters = Clusters(units, 6)


        des = (
            Design()
                .within_subjects(treatment)
                .counterbalance(treatment)
                .limit_groups(len(treatment))
        )



        assign(clusters, des)

        for x in range(1, clusters.n+1):
            cluster_units = clusters.get_units(x)
            for i in range(len(cluster_units)):
                assert units.get_plan(cluster_units[i]) == clusters.get_plan(x)

        

if __name__ == '__main__':
    unittest.main(argv=['first-arg-is-ignored'], exit=False)