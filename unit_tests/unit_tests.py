import sys
sys.path.append("../src")
import numpy as np
from z3 import *
from planet.variable import ExperimentVariable, multifact
from planet.design import Design
from planet.nest import nest
from planet.cross import cross
from planet.solver import BitVecSolver
from planet.plans import PlanGenerator
from planet import *
import unittest
import pandas as pd

from collections import Counter, defaultdict

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
        output = PlanGenerator(des, 4).generate()

        expected_results = {
                ('latex-1-creation', 'ffl-2-creation', 'latex-1-editing', 'ffl-2-editing'),
                ('ffl-2-creation', 'latex-1-creation', 'ffl-2-editing', 'latex-1-editing'),
                ('latex-2-creation', 'ffl-1-creation', 'latex-2-editing', 'ffl-1-editing'),
                ('ffl-1-creation', 'latex-2-creation', 'ffl-1-editing', 'latex-2-editing')
            }

        # the tool should output the expected plans above in any order
        output = set(tuple(plan) for plan in output)

        assert len(output) == 4
        assert expected_results == output



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

        output = PlanGenerator(des, 4).generate()

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
        
        expected_results = set(tuple(plan) for plan in expected_results)
        output = set(tuple(plan) for plan in output)

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

        output = PlanGenerator(des, 4).generate()

        possible_results = [ 
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

        possible_results = set(tuple(tuple(plan) for plan in model) for model in possible_results)
        output = tuple(tuple(list(plan)) for plan in [[str(element) for element in plan] for plan in output])

        assert output in possible_results

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
        
        output = PlanGenerator(des, 4).generate()
      
        possible_results = [ 
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

        possible_results = set(tuple(tuple(plan) for plan in model) for model in possible_results)
        output = tuple(tuple(list(plan)) for plan in [[str(element) for element in plan] for plan in output])

        assert output in possible_results


class TestSolver(unittest.TestCase):
    def test_latinsquare_sat(self):
        v1 = ExperimentVariable(
            name = "v1",
            options = ["a", "b", "c"]
        )
       
        variables = [v1]
        shape = (3, 3)

        solver = BitVecSolver(shape, variables)
        solver.counterbalance([(0, 3, 1), (0, 3, 1)], variables)

        # NOTE: this is a 3x3 latin square 
        expect_sat = [0, 1, 2, 1, 2, 0, 2, 0, 1]
        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_variables[i] == expect_sat[i])
   
        self.assertEqual(solver.solver.check(), sat)

    def test_latinsquare_unsat(self):
        v1 = ExperimentVariable(
            name = "v1",
            options = ["a", "b", "c"]
        )
       
        variables = [v1]
        shape = (3, 3)

        solver = BitVecSolver(shape, variables)
        solver.counterbalance([(0, 3, 1), (0, 3, 1)], variables)

        # NOTE: 0 appears twice in column 2
        expect_sat = [0, 1, 2, 1, 0, 2, 2, 0, 1]
        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_variables[i] == expect_sat[i])
   
        self.assertEqual(solver.solver.check(), unsat)

    def test_degree2_sat(self):
        v1 = ExperimentVariable(
            name="v1",
            options=["a", "b"]
        )

        variables = [v1]
        shape = (2, 2)

        solver = BitVecSolver(shape, variables)
        solver.match_block(v1, block=[(0, 1, 1), (0, 2, 1)])

        # NOTE: this is a 2x2 solution where 0 appears twice in column 1
        expect_sat = [0, 0, 1, 0]
        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_variables[i] == expect_sat[i])

        self.assertEqual(solver.solver.check(), sat)

    def test_match_unsat(self):
        v1 = ExperimentVariable(
            name="v1",
            options=["a", "b"]
        )

        variables = [v1]
        shape = (2, 2)

        solver = BitVecSolver(shape, variables)
        solver.match_block(v1, block=[(0, 1, 1), (0, 2, 1)])

        # NOTE: 0 appears twice in column 2
        expect_sat = [0, 1, 1, 0]
        for i in range(len(expect_sat)):
            solver.solver.add(solver.bitvectors.z3_variables[i] == expect_sat[i])

        self.assertEqual(solver.solver.check(), unsat)

class TestAssignment(unittest.TestCase):
    def test_randomization(self):
        interface = ExperimentVariable(
            name = "interface",
            options = ["AR", "VR", "Reality"]
        )


        units = Units(9)

        design = (
            Design()
                .within_subjects(interface)
                .counterbalance(interface)
                .limit_plans(len(interface))
        )

        
        # Initialize: {pid: {position: Counter({treatment: count})}}
        unit_to_treatment_counts = {f"unit_{i}": {f"pos_{j}":{treatment:0 for treatment in interface.conditions} for j in range(3)} for i in range(1, 10)}
        plans = None

        # Process dataframes
        for _ in range(1000):
            assignment = assign(units, design)
            df = assignment.format_assignment()
            plans = assignment.computed_plans

            for _, row in df.iterrows():
                unit = row['pid']
                plan = row['plan']

                if plan >= 0: 
                    for pos in range(3):
                        treatment = plans[plan][pos]
                        unit_to_treatment_counts[f"unit_{unit}"][f"pos_{pos}"][treatment] += 1

        # Build with MultiIndex columns
        rows = []
        for unit, positions in unit_to_treatment_counts.items():
            row = {}
            for position, treatments in positions.items():
                total = sum(treatments.values())
                for treatment, count in treatments.items():
                    prob = count / total if total > 0 else 0
                    # Use tuple for MultiIndex: (position, treatment)
                    row[(position, treatment)] = prob
            rows.append(row)

        prob_df = pd.DataFrame(rows)

        # Set unit as index
        prob_df.index = unit_to_treatment_counts.keys()
        prob_df.index.name = 'unit'

        # Create proper MultiIndex for columns
        prob_df.columns = pd.MultiIndex.from_tuples(
            prob_df.columns,
            names=['position', 'treatment']
        )

        # Sort
        prob_df = prob_df.sort_index(axis=1).round(2)

        # Expected probability (uniform across 3 treatments)
        expected_prob = 1/3

        # Tolerance for floating point comparison (due to sampling variation)
        tolerance = 0.05  # Allow 5% deviation

        # Test 1: Each probability should be close to 1/3
        assert np.all(np.abs(prob_df.values - expected_prob) < tolerance), \
            "Some probabilities deviate significantly from 1/3"

        # Test 2: For each (unit, position), probabilities sum to 1
        for pos in ['pos_0', 'pos_1', 'pos_2']:
            cols = prob_df.columns[prob_df.columns.get_level_values(0) == pos]
            row_sums = prob_df[cols].sum(axis=1)
            assert np.allclose(row_sums, 1.0, atol=0.01), \
                f"Probabilities for {pos} don't sum to 1"

        # Test 3: No treatment is systematically favored
        # Mean probability across all units and positions should be ~1/3
        mean_prob = prob_df.values.mean()
        assert np.abs(mean_prob - expected_prob) < 0.02, \
            f"Mean probability {mean_prob:.3f} deviates from expected {expected_prob:.3f}"

        # Test 4: Standard deviation should be small (indicates balance)
        std_prob = prob_df.values.std()
        assert std_prob < 0.03, \
            f"Standard deviation {std_prob:.3f} too high, indicates imbalance"
   
if __name__ == '__main__':
    unittest.main(argv=['first-arg-is-ignored'], exit=False)