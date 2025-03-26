import sys
sys.path.append("../src")

from z3 import *
from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest, cross
from lib.unit import Units
from lib.assignment import assign
from lib.solver import BitVecSolver
import numpy as np
import unittest

class TestSolver(unittest.TestCase):
    def test_latinsquare_sat(self):
        v1 = ExperimentVariable(
            name = "v1",
            options = ["a", "b", "c"]
        )
       
        variables = [v1]
        shape = (3, 3)

        solver = BitVecSolver(shape, variables)
        solver.counterbalance([], variables)

        # NOTE: this is a 3x3 latin square 
        expect_sat = [0, 1, 2, 1, 2, 0, 2, 0, 1]
        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_representation[i] == expect_sat[i])
   
        self.assertEqual(solver.solver.check(), sat)

    def test_latinsquare_unsat(self):
        v1 = ExperimentVariable(
            name = "v1",
            options = ["a", "b", "c"]
        )
       
        variables = [v1]
        shape = (3, 3)

        solver = BitVecSolver(shape, variables)
        solver.counterbalance([], variables)

        # NOTE: 0 appears twice in column 2
        expect_sat = [0, 1, 2, 1, 0, 2, 2, 0, 1]
        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_representation[i] == expect_sat[i])
   
        self.assertEqual(solver.solver.check(), unsat)

    def test_match_sat(self):
        v1 = ExperimentVariable(
            name = "v1",
            options = ["a", "b"]
        )
       
        variables = [v1]
        shape = (2, 2)

        solver = BitVecSolver(shape, variables)
        solver.match_block(v1, block=[(0, 1, 1), (0, 2, 1)])

        # NOTE: 0 appears twice in column 2
        expect_sat = [0, 0, 1, 0]

        print()
        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_representation[i] == expect_sat[i])

        
   
        self.assertEqual(solver.solver.check(), sat)

    def test_match_unsat(self):
        v1 = ExperimentVariable(
            name = "v1",
            options = ["a", "b"]
        )
       
        variables = [v1]
        shape = (2, 2)

        solver = BitVecSolver(shape, variables)
        solver.match_block(v1, block=[(0, 1, 1), (0, 2, 1)])

        # NOTE: 0 appears twice in column 2
        expect_sat = [0, 1, 1, 0]

        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_representation[i] == expect_sat[i])

        
   
        self.assertEqual(solver.solver.check(), unsat)


if __name__ == '__main__':
    unittest.main(argv=['first-arg-is-ignored'], exit=False)