import sys
sys.path.append("../src")

from z3 import *
from planet.variable import ExperimentVariable, multifact
from planet.design import Design
from planet.nest import nest
from planet.cross import cross
from planet.unit import Units
from planet.assignment import assign
from planet.solver import BitVecSolver
import unittest



def hashable_set(models):
    output = []
    for i in range(len(models)):
                model = []
                for j in range(len(models[i])):
                    plan = tuple(models[i][j])
                    model.append(plan)
                output.append(tuple(model))
    
    return sorted(output, key=hash)
    


# NOTE: all of these are assuming some seed. 
class TestDSL(unittest.TestCase):



    def test_ffl(self):
        task = ExperimentVariable(
            name = "task",
            options = ["creation", "editing"]
        )

        number = ExperimentVariable(
            name = "number",
            options = ["1", "2"]
        )

        interface = ExperimentVariable(
            name = "interface",
            options = ["ffl", "latex"]
        )


        units = Units(16)

        task_des = (
            Design()
                .within_subjects(task)
                .start_with(task, "creation")
        )


        interface_des = (
            Design()
                .within_subjects(interface)
                .counterbalance(interface)
        )

        number_des = (
            Design()
                .within_subjects(number)
                .counterbalance(number)
            
        )

        cross_des = cross(interface_des, number_des)
        des = nest(inner=cross_des, outer=task_des)
        output = des.eval(test=True)

        expected_results = [
             [
                ['latex-1-creation', 'ffl-2-creation', 'latex-1-editing', 'ffl-2-editing'],
                ['ffl-2-creation', 'latex-1-creation', 'ffl-2-editing', 'latex-1-editing'],
                ['latex-2-creation', 'ffl-1-creation', 'latex-2-editing', 'ffl-1-editing'],
                ['ffl-1-creation', 'latex-2-creation', 'ffl-1-editing', 'latex-2-editing']
             ]
        ]

        output = hashable_set(output)
        expected_results = hashable_set(expected_results)[0]


        assert len(output) == 8
        assert expected_results in output

    def test_nest_as_latinsquare(self):
        # nest is a subset of latin-square
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

        des = nest(inner=des1, outer=des2)

        factorial = multifact([treatment, task])

        latinsquare = (
            Design()
                .within_subjects(factorial)
                .counterbalance(factorial)
                .limit_plans(len(factorial))
        )
        
        
        nest_output = des.eval(test=True)
        latin_square_output = latinsquare.eval(test=True)

        latin_square_output = set(hashable_set(latin_square_output))
        nest_output = set(hashable_set(nest_output))
        
        assert len(latin_square_output.difference(nest_output)) == len(latin_square_output) - len(nest_output)


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
        
        expected_results = hashable_set([expected_results])
        output = hashable_set([output])

        assert len(output) == len(expected_results)
        assert output == expected_results

    def test_latin_square(self):
        treatment = ExperimentVariable(
            name = "treatment",
            options = ["a", "b", "c"]
        )

        des = (
            Design()
                .within_subjects(treatment)
                .counterbalance(treatment)
                .limit_plans(len(treatment))
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
        

        expected_results = hashable_set(expected_results)
        output = hashable_set(output)

        assert len(output) == len(expected_results)

   
        assert output == expected_results
       


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

        des = nest(inner=des1, outer=des2)
        
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

        expected_results = hashable_set(expected_results)
        output = hashable_set(output)

        assert len(output) == len(expected_results)
        assert output == expected_results


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


if __name__ == '__main__':
    unittest.main(argv=['first-arg-is-ignored'], exit=False)