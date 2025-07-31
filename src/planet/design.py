# External dependencies
from z3 import *  # requires `pip install z3-solver`
import math
import pandas as pd
from planet.logger import logger
# Internal modules (installed via `pip install -e .`)
from planet.unit import Groups
from planet.orders import Sequence
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

class Plans:
    def __init__(self):
        self.variables = [] 
        self.groups = Groups()
        self.constraints = ConstraintManager()
        self.trials = 0
        self.designer = Designer()
        self.plans = None
        self.random_var = []
        self.previous_snapshot = None
        self.design_variables = {}

    
    def _add_design_variable(self, variable):
        if variable not in self.design_variables:
            self.design_variables[variable] = DesignVariable(variable)

    def add_variable(self, variable, within_subjects=False):
        assert isinstance(variable, ExperimentVariable)

        # FIXME
        self._add_design_variable(variable)

        if isinstance(variable, MultiFactVariable):
            variables = variable.variables
        else:
            variables = [variable]
   
        self.variables.extend(variables)



    def add_variables(self, variables:list):
        for v in variables:
            self.add_variable(v, True)
  

class RandomPlan(Plans):
    """This is like creating a vector of random variables."""
    def __init__(self, variables):
        super().__init__()
        for var in variables:
            self.add_variable(var, True)
            self.random_var = [var]
            
        self.groups.set_num_plans(1)
        self.constraints.add_constraint(NoRepeat(self.random_var[0], self.get_width()))

    def num_trials(self, n):
        self.trials = n
        return self
    
    
    
    def get_width(self):
        return self.trials 

class Design(Plans):
    """Main class for creating experimental designs."""
    def __init__(self):
        super().__init__()

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
    def has_random_variable(self):
        return bool(self.random_var)
    
    @property
    def is_random(self):
        return not self.counterbalanced
    


    def to_latex(self):
        # FIXME: won't work with random plans
        matrix = self.get_plans()
        formatter = LatexExport(matrix)
        formatter.to_latex()

    def num_trials(self, n):
        self.trials = n
        return self
    
    def between_subjects(self, variable):
        self.add_variable(variable)
        self.trials = 1 if not self.trials else self.trials

        # enforces repeating trials when specified with within subjects variables
        self.constraints.add_constraint(
            InnerBlock(
                variable,
                0,
                1
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
        self.add_variable(variable, True)
        self.trials = len(variable)
        self.add_constraint(NoRepeat(variable, width=self.trials))
        return self
    
    def limit_groups(self, n):
        self.groups.set_num_plans(n)
        return self
    
    """
    Deals with random variables. Opportunity to decouple? 
    """
    def _determine_random_width(self, rand):
        width = self.get_width()
        div = 1
        for constraint in self.constraints.get_constraints_for_variable(rand):
            if isinstance(constraint, OuterBlock):
                width = constraint.width
  
            elif isinstance(constraint, InnerBlock):
                div = constraint.width
        
        return int(width/div)
    

    def _determine_random_span(self, rand):
        span = 1
        for constraint in self.constraints.get_constraints_for_variable(rand):
            if isinstance(constraint, InnerBlock):
               span = constraint.width
        return span
    
    def _instantiate_random_variables(self, n, rand):
        # NOTE to self: this will only work if there is one random variable :)
        """
        Think about this like instantiating the elements of a matrix of random variables
        """
        assert self.plans is not None

        width = self._determine_random_width(rand)
        span = self._determine_random_span(rand)
        variables = rand.variables if isinstance(rand, MultiFactVariable) else [rand]

        random_index = self.variables.index(variables[0])
        randomizer = Randomizer(rand, width, span, int(n*self.get_width()/width/span))
        self.plans = randomizer.apply_randomization(width, span, random_index, n, self.plans)


    def snapshot(self):
        groups = len(self.groups)
        constraint_ids = self.constraints.stringified()
        signature = "_".join(constraint_ids) + f"_{self.get_width()}_{groups}"
        return hashlib.sha256(signature.encode()).hexdigest()

    def _eval_plans(self, n = None):
    
        self.identify_random_vars()
        if self.is_empty:
            return []
        
        elif self.is_random:
            prev = len(self.groups)
            self.groups.set_num_plans(1)
     
        self.eval()
        self.previous_snapshot = self.snapshot()

        if self.has_random_variable:
            assert n is not None
            n = math.ceil(n/len(self.plans)) * len(self.plans)
            for rand in self.random_var:
                rand = self._construct_var(rand)
                self._instantiate_random_variables(n, rand)

        if self.is_random:
            self.groups.set_num_plans(prev)

            

    def check_plans(self, plans):
        if len(self.plans) <= 0:
            raise DesignError("The constraints specified on this design are not compatible")
    
    def get_plans(self, n = None):
   
        if self.plans is None or self.is_modified:
           self._eval_plans(n)

        try:
            self.check_plans(self.plans)
        except DesignError as e:
            logger.warning("Design results in no viable plans. Consider a different experiment.")
            

        
        return self.plans
    
    
    def get_width(self):
        return self.trials 
    
    
    def extract_counterbalance_info(self, var):
        """Extract variables and condition count"""
        return (len(var.get_variables()), len(var))
    
    def _determine_num_plans(self):
  
        """Determine the number of experimental plans based on constraints and trial width."""
        if len(self.groups) > 0:
            return self.groups  # Assume already set

        counterbalance_info = []
        rankings = []

        for variable in self.design_variables:
            if self.design_variables[variable].is_counterbalanced:
                group = self.extract_counterbalance_info(variable)
                counterbalance_info.append(group)

            elif self.design_variables[variable].is_ranked:
                rankings.append(count_values(self.design_variables[variable].get_ranks()))
               
        self.groups.calculate_num_plans(counterbalance_info, rankings, self.trials)
    

    def _eval(self):
        # Get the width of the design
        width = self.get_width()
        sequence = Sequence(width)
        self._determine_num_plans()
        

        self.designer.start(
            self.groups, 
            sequence, 
            self.variables
        )

        
        # NOTE: ensure no downstream effects :)
        # self.designer.solver.all_different()
        self.designer.eval_constraints(self.constraints.get_constraints(), self.groups, width)

    def test_eval(self):
        self._eval()
        return self.designer.eval_all()
        

    def eval(self):
        assert not self.is_empty
        self._eval()
        plans = self.designer.eval()
        self.plans = plans


    def identify_random_vars(self):
        self.random_var.extend([
            v for v, obj in self.design_variables.items()
            if not (obj.is_counterbalanced or obj.is_ranked)
        ])
            
    
    def _construct_var(self, variable):
        if isinstance(variable, MultiFactVariable):
            variables = variable.variables
            return variables[0] if len(variables) == 1 else multifact(variables)
        else:
            return variable
        
    # def get_design_specification(self):
    #     return {
    #         "constraints":
    #         "variables":
    #         "Design"
    #     }
       
  
