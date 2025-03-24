import sys
sys.path.append("../src")

from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design, nest
from lib.unit import Units
from lib.assignment import assign
import numpy as np
import unittest

# NOTE: all of these are assuming some seed. 
class TestDesigns(unittest.TestCase):
    def test_full_counterbalance(self):
        treatment = ExperimentVariable(
            name = "treatment",
            options = ["a", "b", "c", "d"]
        )

        des = (
            Design()
                .within_subjects(treatment)
                .counterbalance(treatment)
        )

        output = des.eval()

        expected_results = [['b', 'c', 'd', 'a'],
                    ['a', 'd', 'c', 'b'],
                    ['c', 'b', 'a', 'd'],
                    ['d', 'a', 'b', 'c'],
                    ['d', 'a', 'c', 'b'],
                    ['c', 'b', 'd', 'a'],
                    ['b', 'c', 'a', 'd'],
                    ['a', 'd', 'b', 'c'],
                    ['a', 'c', 'd', 'b'],
                    ['b', 'd', 'c', 'a'],
                    ['c', 'a', 'd', 'b'],
                    ['d', 'b', 'c', 'a'],
                    ['d', 'b', 'a', 'c'],
                    ['b', 'd', 'a', 'c'],
                    ['a', 'c', 'b', 'd'],
                    ['c', 'a', 'b', 'd'],
                    ['d', 'c', 'a', 'b'],
                    ['d', 'c', 'b', 'a'],
                    ['c', 'd', 'b', 'a'],
                    ['c', 'd', 'a', 'b'],
                    ['b', 'a', 'd', 'c'],
                    ['a', 'b', 'd', 'c'],
                    ['b', 'a', 'c', 'd'],
                    ['a', 'b', 'c', 'd'],]
        
        np.testing.assert_array_equal(output, expected_results)

    def test_latin_square(self):
        treatment = ExperimentVariable(
            name = "treatment",
            options = ["a", "b", "c"]
        )

        des = (
            Design()
                .within_subjects(treatment)
                .counterbalance(treatment)
                .limit_groups(len(treatment))
        )

        output = des.eval(test=True)

        expected_results = [ 
            [['c', 'b', 'a'],
              ['a', 'c', 'b'],
              ['b', 'a', 'c']],
              [['c', 'a', 'b'],
       ['a', 'b', 'c'],
       ['b', 'c', 'a']],
       [['a', 'b', 'c'],
       ['b', 'c', 'a'],
       ['c', 'a', 'b']],
       [['a', 'c', 'b'],
       ['b', 'a', 'c'],
       ['c', 'b', 'a']],
       [['b', 'c', 'a'],
       ['a', 'b', 'c'],
       ['c', 'a', 'b']],
       [['c', 'b', 'a'],
       ['b', 'a', 'c'],
       ['a', 'c', 'b']],
       [['b', 'a', 'c'],
       ['c', 'b', 'a'],
       ['a', 'c', 'b']],
       [['b', 'a', 'c'],
       ['a', 'c', 'b'],
       ['c', 'b', 'a']],
       [['a', 'b', 'c'],
       ['c', 'a', 'b'],
       ['b', 'c', 'a']],
       [['a', 'c', 'b'],
       ['c', 'b', 'a'],
       ['b', 'a', 'c']],
       [['b', 'c', 'a'],
       ['c', 'a', 'b'],
       ['a', 'b', 'c']],
       [['c', 'a', 'b'],
       ['b', 'c', 'a'],
       ['a', 'b', 'c']]
        ]
        
        assert len(output) == len(expected_results)

        for i in range(len(output)):
            np.testing.assert_array_equal(output[i], expected_results[i])


    def test_nest(self):
        treatment = ExperimentVariable(
            name = "treatment",
            options = ["a", "b"]
        )

        task = ExperimentVariable(
            name = "task",
            options = ["1", "2"]
        )

        des1 = (
            Design()
                .within_subjects(treatment)
                .counterbalance(treatment)
        )

        des2 = (
            Design()
                .within_subjects(task)
                .counterbalance(task)
        )

        des = nest(des1, des2)
        
        output = des.eval(test=True)
      
        expected_results = [ 
            [['a-2', 'b-2', 'a-1', 'b-1'],
       ['b-2', 'a-2', 'b-1', 'a-1'],
       ['a-1', 'b-1', 'a-2', 'b-2'],
       ['b-1', 'a-1', 'b-2', 'a-2']],
              [['b-1', 'a-1', 'b-2', 'a-2'],
       ['a-1', 'b-1', 'a-2', 'b-2'],
       ['b-2', 'a-2', 'b-1', 'a-1'],
       ['a-2', 'b-2', 'a-1', 'b-1']],

       [['a-1', 'b-1', 'a-2', 'b-2'],
       ['b-1', 'a-1', 'b-2', 'a-2'],
       ['a-2', 'b-2', 'a-1', 'b-1'],
       ['b-2', 'a-2', 'b-1', 'a-1']],

       [['b-2', 'a-2', 'b-1', 'a-1'],
       ['a-2', 'b-2', 'a-1', 'b-1'],
       ['b-1', 'a-1', 'b-2', 'a-2'],
       ['a-1', 'b-1', 'a-2', 'b-2']]
        ]
        
        assert len(output) == len(expected_results)

        for i in range(len(output)):
            np.testing.assert_array_equal(output[i], expected_results[i])
        

if __name__ == '__main__':
    unittest.main(argv=['first-arg-is-ignored'], exit=False)