from z3 import *
from planet import *
import unittest
import duckdb


def is_unique(col):
    arr = col.to_numpy() 
    return (arr[0] == arr).all()

class TestSolver(unittest.TestCase):
    def test_latinsquare_sat(self):
        count = ExperimentVariable(
            name = "count",
            options = ["1", "2", "3"]
        )
        units = Units(27)

        des = (
            Design()
                .within_subjects(count)
                .counterbalance(count)
                .limit_plans(len(count))
        )


        assignment = assign(units, des)
        df = duckdb.sql(f"select count(pid) from {assignment.units.table} group by plan").df()
        assert is_unique(df["count(pid)"])
        

if __name__ == '__main__':
    unittest.main(argv=['first-arg-is-ignored'], exit=False)