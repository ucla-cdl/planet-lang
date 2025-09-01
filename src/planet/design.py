# External dependencies
from z3 import *  # requires `pip install z3-solver`
import math
import pandas as pd
# Internal modules (installed via `pip install -e .`)
from planet.unit import Groups
from planet.variable import MultiFactVariable, multifact
from planet.constraint import (
    StartWith, Counterbalance, NoRepeat,
    InnerBlock, OuterBlock, Constraint,
    SetRank, SetPosition, AbsoluteRank
)
from planet.designer import Designer
from planet.randomizer import Randomizer
from planet.formatter import LatexExport
from planet.candl import *
from planet.candl import generate_conditions
from planet.helpers import *
from planet.narray import *
from planet.constraint_manager import ConstraintManager
import hashlib
from planet.design_variable import DesignVariable
from planet.design_exceptions import *

  
# # TODO: 
#     1. better handling of rand_variables
#     2. separate constraintspec from the actual constraint
#     3. identify patter when copying constraints (in nest and cross)

class Design:
    """Main class for creating experimental designs."""
    def __init__(self):
        self.variables = [] 
        self.groups = Groups()
        self.constraints = ConstraintManager()
        self.trials = 0
        self.designer = Designer()
        self.previous_snapshot = None
        self.design_variables = {}

    @property
    def maximum_trials(self):
        max_width = min(spec.max_width() for spec in self.design_variables.values())
        return max_width

    # FIXME: this is slow
    @property
    def within_subjects_variables(self):
        return [var for var in self.design_variables if not self.design_variables[var].is_repeated]


    @property
    def is_constrained(self):
        # FIXME: not handled for replicated trials
        return self.constraints.check_property(lambda c: isinstance(c, (OuterBlock, InnerBlock)))
    
    @property
    def counterbalanced(self):
        # FIXME: not handled for replicated trials
        return self.constraints.check_property(lambda c: isinstance(c, (Counterbalance, AbsoluteRank)))
   
    @property
    def is_empty(self):
        # FIXME: not handled for replicated trials
        return not self.variables 

    @property
    def is_modified(self):
        return self.snapshot() != self.previous_snapshot
    
    @property
    def is_random(self):
        return not self.counterbalanced and not self.is_empty
    

    def num_plans(self):
        self._determine_num_plans()
        return 1 if self.is_empty or self.is_random else self._determine_num_plans()

    def num_trials(self, n):
        if self.trials:
            print(self.trials)
            raise ValueError("It appears num_trials was already specified for this design. You can only set the number of trials once.")

        self.trials = n
        return self
    
    def between_subjects(self, variable):
        self.add_variable(variable)
        # self.trials = 1 if self.trials == 0 else self.trials

        # enforces repeating trials when specified with within subjects variables
        self.add_constraint(
            InnerBlock(
                variable,
                0,
                1,
                [1,1]
                )
            )
        return self
    
    def counterbalance(self, variable:ExperimentVariable, w = 0, h = 0, stride = [1, 1]):
        self.add_constraint(Counterbalance(variable, width = w, height = h, stride = stride))
        return self
    
    def start_with(self, variable:ExperimentVariable, condition):
        condition = as_list(condition)
        rank = 1
        for c in condition:
            self.absolute_rank(variable, c, rank)
        rank+=1
  
        return self
    
    def set_position(self, variable:ExperimentVariable, condition, pos):
        self.add_constraint(SetPosition(variable, condition, pos))
        return self
    
    def set_rank(self, variable:ExperimentVariable, condition, rank, condition2):
        self.add_constraint(SetRank(variable, condition, rank, condition2))
        return self
    
    def absolute_rank(self, variable:ExperimentVariable, condition, rank):
        constraint = self.constraints.add_absolute_rank(variable, condition, rank)
        self.design_variables[variable].add_constraint(constraint)
        return self
    
    def add_constraint(self, constraint):
        self.constraints.add_constraint(constraint)
        self._add_design_variable(constraint.variable)
        self.design_variables[constraint.variable].add_constraint(constraint)

    def add_constraints(self, constraints:list):
        for c in constraints:
            self.add_constraint(c)

    def within_subjects(self, variable):
        self.add_variable(variable)
        self.add_constraint(NoRepeat(variable, width=len(variable)))
        return self
    
    def limit_plans(self, n):
        self.groups.set_num_plans(n)
        return self

    def snapshot(self):
        groups = self.num_plans()
        constraint_ids = self.constraints.stringified()
        signature = "_".join(constraint_ids) + f"_{self.get_width()}_{groups}"
        return hashlib.sha256(signature.encode()).hexdigest()
    
    def get_width(self):
        return self.trials if self.trials else len(next(iter(self.design_variables)))
    
    def extract_counterbalance_info(self, var):
        """Extract variables and condition count"""
        return (len(var.get_variables()), len(var))
    
    def calculate_num_plans(self, counterbalanced_groups, rankings, num_trials):
        """Determine the number of experimental plans based on constraints and trial width."""
        total_n_plans = 1

        for variables, num_conditions in counterbalanced_groups:
                num_trials = num_trials
                total_n_plans *= calculate_plan_multiplier(num_conditions, variables, num_trials)
        for ranking in rankings:
            total_n_plans *= factorial_product_of_counts(ranking)

        return int(total_n_plans)
    
    def _determine_num_plans(self):
        """Determine the number of experimental plans based on constraints and trial width."""
        if len(self.groups) > 0:
            return len(self.groups)  # already specified by user

        counterbalance_info = []
        rankings = []

        for variable in self.design_variables:
            if self.design_variables[variable].is_counterbalanced:
                group = self.extract_counterbalance_info(variable)
                counterbalance_info.append(group)

            elif self.design_variables[variable].is_ranked:
                rankings.append(count_values(self.design_variables[variable].get_ranks()))

        return self.calculate_num_plans(counterbalance_info, rankings, self.get_width())

    def test_eval(self):
        self.designer.start(self)
        return self.designer.eval_all()
        

    def identify_random_vars(self):
        return [
            v for v, obj in self.design_variables.items()
            if not (obj.is_counterbalanced or obj.is_ranked)
        ]
            
    def _add_design_variable(self, variable):
        if variable not in self.design_variables:
            self.design_variables[variable] = DesignVariable(variable)

    def add_variable(self, variable):
        assert isinstance(variable, ExperimentVariable)

        # FIXME
        if variable in self.design_variables: 
            raise ValueError(f"Cannot add variable '{variable}' — it already exists in design.")
        
        self._add_design_variable(variable)

        if isinstance(variable, MultiFactVariable):
            variables = variable.variables
        else:
            variables = [variable]
    
        self.variables.extend(variables)
        # ensures no duplicates and preserves order 
        self.variables = list(dict.fromkeys(self.variables))

    def add_variables(self, variables:list):
        for v in variables:
            self.add_variable(v)

    def get_constraints(self):
        return self.constraints.get_constraints()
    
