# External dependencies
from z3 import *  # requires `pip install z3-solver`
import math
import pandas as pd
# Internal modules (installed via `pip install -e .`)
from planet.unit import Groups
from planet.variable import MultiFactVariable, multifact
from planet.constraint import (
    Counterbalance, NoRepeat,
    InnerBlock, OuterBlock,
    SetRank, SetPosition, AbsoluteRank, Constraint
)
from planet.designer import Designer
from planet.candl import *
from planet.helpers import *
from planet.narray import *
from planet.constraint_manager import ConstraintManager
import hashlib
from planet.design_variable import DesignVariable
from planet.design_exceptions import *
from typing import List, Dict, Optional
from planet.region import DesignRegion


class Design:
    """Main class for creating experimental designs."""
    def __init__(self):
        self.variables:List[ExperimentVariable] = [] 
        self.num_groups:int = 0
        self.constraints:ConstraintManager = ConstraintManager()
        self.trials:int = 0
        self.designer:Designer = Designer()
        self.previous_snapshot:Optional[str] = None
        self.design_variables:Dict[str, DesignVariable] = {}

        self._minimum_trials = 1

    @property
    def maximum_trials(self):
        def is_not_in_multifact(spec:Dict) -> bool:
            """
            Check if a variable is not part of a multifact variable.

            A variable is considered part of a multifact variable if:
            - It is repeated.
            - It is counterbalanced.
            - It is not blocked as an inner variable.
            """
            return not (spec.is_repeated and spec.is_counterbalanced and not spec.is_blocked_inner)

        # the maximum width is the smallest maximum width of all variables in
        # the design. The maximum width of a variables is determined by its
        # constraints. 
        valid_variables = (spec for spec in self.design_variables.values() if is_not_in_multifact(spec))
        max_width = min(spec.max_width() for spec in valid_variables)

        return max_width
    
    def set_minimum_trials(self, n:int):
        self._minimum_trials = n

    # FIXME: this is slow
    @property
    def within_subjects_variables(self):
        return [var for var in self.design_variables if not self.design_variables[var].is_repeated]

    @property
    def is_constrained(self) -> bool:
        return self.constraints.check_property(lambda c: isinstance(c, (OuterBlock, InnerBlock)))
    
    @property
    def counterbalanced(self) -> bool:
        return self.constraints.check_property(lambda c: isinstance(c, (Counterbalance, AbsoluteRank)))
   
    @property
    def is_empty(self) -> bool:
        return not self.variables 

    @property
    def is_modified(self) -> bool:
        return self.snapshot() != self.previous_snapshot
    
    @property
    def is_random(self) -> bool:
        return not self.counterbalanced and not self.is_empty
    
    def num_plans(self) -> int:
        self._determine_num_plans()
        return 1 if self.is_empty or self.is_random else self._determine_num_plans()

    def num_trials(self, n: int) -> "Design":
        self.trials = n
        return self
    
    def between_subjects(self, variable:ExperimentVariable) -> "Design":
        self.add_variable(variable)

        # ensures repeating trials when specified with within subjects variables
        self.add_constraint(
            InnerBlock(
                variable,
                DesignRegion(0, 1, [1,1])
                )
            )
        return self
    
    def counterbalance(self, variable:ExperimentVariable, w = 0, h = 0, stride = [1, 1]):
        self.add_constraint(Counterbalance(variable, width = w, height = h, stride = stride))
        return self
    
    def start_with(self, variable:ExperimentVariable, condition:str) -> "Design":
        condition = as_list(condition)
        rank = 1
        for c in condition:
            self.absolute_rank(variable, c, rank)
        rank+=1
  
        return self

    def absolute_rank(self, variable:ExperimentVariable, condition:str, rank:int) -> "Design":
        constraint = self.constraints.add_absolute_rank(variable, condition, rank)
        self.design_variables[variable].add_constraint(constraint)
        return self
    
    def add_constraint(self, constraint:Constraint) -> None:
        self.constraints.add_constraint(constraint)
        self._add_design_variable(constraint.variable)
        self.design_variables[constraint.variable].add_constraint(constraint)

    def add_constraints(self, constraints:list[Constraint]) -> None:
        for c in constraints:
            self.add_constraint(c)

    def within_subjects(self, variable:ExperimentVariable) -> "Design":
        self.add_variable(variable)
        # by default, within subjects variables do not repeat!
        self.add_constraint(NoRepeat(variable, width=len(variable)))
        return self
    
    def limit_plans(self, n:int) -> "Design":
        self.num_groups = n
        return self

    def snapshot(self) -> str:
        groups = self.num_plans()
        constraint_ids = self.constraints.stringified()
        signature = "_".join(constraint_ids) + f"_{self.get_width()}_{groups}"
        return hashlib.sha256(signature.encode()).hexdigest()
    
    def get_width(self) -> int:
        return self.trials if self.trials else len(next(iter(self.design_variables)))
    
    def extract_counterbalance_info(self, var:ExperimentVariable) -> tuple[int, int]:
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
        counterbalance_info = []
        rankings = []
        plans_precomputed = False 

        for variable in self.design_variables:
            if self.design_variables[variable].is_counterbalanced:
                group = self.extract_counterbalance_info(variable)
                counterbalance_info.append(group)

            elif self.design_variables[variable].is_ranked:
                rankings.append(count_values(self.design_variables[variable].get_ranks()))

            if self.constraints.has_constraint(variable, InnerBlock) or self.constraints.has_constraint(variable, OuterBlock):
                plans_precomputed = True

        plan_count = self.calculate_num_plans(counterbalance_info, rankings, self.get_width())

        if self.num_groups > 0:
            lcm = self._determine_LCM()
            num_plans = (self.num_groups // lcm) * lcm
            if num_plans == 0: 
                raise ValueError(f"Number of plans ({self.num_groups}) is too small to accommodate counterbalancing constraints. Minimum number of plans needed is {lcm}.")
            
            plan_count = ((self.num_groups // lcm) * lcm) if plans_precomputed else min(plan_count, (self.num_groups // lcm) * lcm)

        return plan_count
    
    def _determine_LCM(self):
        counterbalance_info = []

        for variable in self.design_variables:
            if self.design_variables[variable].is_counterbalanced:
                group = self.extract_counterbalance_info(variable)
                counterbalance_info.append(group)

        """Determine the number of experimental plans based on constraints and trial width."""
        total_n_plans = math.lcm(*(y for _, y in counterbalance_info))
        return int(total_n_plans)
    

    def calculate_lcm(self, counterbalanced_groups):
        """Determine the number of experimental plans based on constraints and trial width."""
        total_n_plans = math.lcm(*counterbalanced_groups.values())
        return int(total_n_plans)

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
    
