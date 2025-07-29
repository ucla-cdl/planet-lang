# External dependencies
from z3 import *  # requires `pip install z3-solver`
import math
import pandas as pd

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

class Plans:
    def __init__(self):
        self.sequence = None
        self.variables = []
        self.ws_variables = []
        self.bs_variables = []
        self.groups = None
        self.constraints = []
        self.trials = 0
        self.designer = Designer()
        self.plans = None
        # test
        self.random_var = []
        self.previous_snapshot = None

    def is_random(self):
        return not self.counterbalanced
    
    #FIXME: come back to this
    def _add_variable(self, variable):
        assert isinstance(variable, ExperimentVariable)

        if isinstance(variable, MultiFactVariable):
            variables = variable.variables
        else:
            variables = [variable]

        self.variables.extend(variables)
        self.ws_variables.extend(variables)

class RandomPlan(Plans):
    """This is like creating a vector of random variables."""
    def __init__(self, variables):
        super().__init__()
        for var in variables:
            self._add_variable(var)
            self.random_var = [var]
            
        self.groups = Groups(1)
        self.constraints.append(NoRepeat(self.random_var[0], self.get_width()))

    def num_trials(self, n):
        self.trials = n
        return self
    
    
    
    def get_width(self):
        return self.trials or math.prod(v.n for v in self.ws_variables)

class Design(Plans):
    """Main class for creating experimental designs."""
    def __init__(self):
        super().__init__()
        self.rank_constraints = {}

        # FIXME
        # var = ExperimentVariable("base", 1)
        # self._add_variable(var)
        # self.constraints.append(Counterbalance(var, width = 0, height = 1, stride = [1,1]))
  
    def to_latex(self):
        # FIXME: won't work with random plans
        matrix = self.get_plans()
        formatter = LatexExport(matrix)
        formatter.to_latex()

    def num_trials(self, n):
        self.trials = n
        return self
    
    def _add_variable(self, variable):
        assert isinstance(variable, ExperimentVariable)

        if isinstance(variable, MultiFactVariable):
            variables = variable.variables
        else:
            variables = [variable]

        self.variables.extend(variables)
        self.ws_variables.extend(variables)
    
    def add_variable(self, variable, l):
        assert isinstance(variable, ExperimentVariable)
        if isinstance(variable, MultiFactVariable):
            variables = variable.variables
        else:
            variables = [variable]

        self.variables.extend(variables)
        l.extend(variables)
    
    def between_subjects(self, variable):
        self.add_variable(variable, self.bs_variables)
        return self

    def within_subjects(self, variable):
        self.add_variable(variable, self.ws_variables)
        width = self.get_width()
        # FIXME: should probably decouble this constraint block concept?
        self.constraints.append(NoRepeat(variable, width=width))
        return self
    
    def limit_groups(self, n):
        self.groups = Groups(n)
        return self
    
    def has_random_variable(self):
        return bool(self.random_var)
    
    
    def _determine_random_width(self, rand):
        width = self.get_width()
        
        div = 1
        for constraint in self.constraints:
            if isinstance(constraint, OuterBlock) and constraint.variable == rand:
                width = constraint.width
  
            elif isinstance(constraint, InnerBlock) and constraint.variable == rand:
                div = constraint.width
        
        return int(width/div)
    

    def _determine_random_span(self, rand):
        span = 1
        for constraint in self.constraints:
            if isinstance(constraint, InnerBlock) and constraint.variable == rand:
               span = constraint.width
        return span
    
    def _instantiate_random_variables(self, n, rand):
        # NOTE to self: this will only work if there is one random variable :)
        """
        Think about this like instantiating the elements of a matrix of random variables
        """
        assert self.plans is not None
        random_index = self.variables.index(rand)
        width = self._determine_random_width(rand)
        span = self._determine_random_span(rand)
        # randomly generates plans for every block of random var. 
        # rand_vars = self._generate_random_variables(int(n*self.get_width()/width/span), self.random_var, width) 
        # self.apply_randomization(rand_vars, width, span, random_index, n)
        randomizer = Randomizer(rand, width, span, random_index, int(n*self.get_width()/width/span), n, self.plans)
        self.plans = randomizer.get_plans()
    
    @property
    def is_modified(self):
        return self.snapshot() != self.previous_snapshot

    def snapshot(self):
        return str(hash(tuple(self.constraints))) + str(self.get_width()) + "_" + str(len(self.groups))

    def get_plans(self, n = None):
        if self.is_empty:
            return []
        elif self.is_random():
            assert n is not None
            return self.random(n)
        if self.plans is not None and not self.is_modified:
            return self.plans
        else:
            self.eval()
            self.previous_snapshot = self.snapshot()
   
        if self.has_random_variable():
            assert n is not None
            n = math.ceil(n/len(self.plans)) * len(self.plans)
            for rand in self.random_var:
                self._instantiate_random_variables(n, rand)
        return self.plans
    
    
    def get_width(self):
        return self.trials or math.prod(v.n for v in self.ws_variables)
    
    def start_with(self, variable, condition):
        assert isinstance(variable, ExperimentVariable)

        condition = as_list(condition)
        rank = 1
        for c in condition:
            self.absolute_rank(variable, c, rank)
        rank+=1
  
        return self
    
    def set_position(self, variable, condition, pos):
        assert isinstance(variable, ExperimentVariable)
        self.constraints.append(SetPosition(variable, condition, pos))
        return self
    
    def set_rank(self, variable, condition, rank, condition2):
        assert isinstance(variable, ExperimentVariable)
        self.constraints.append(SetRank(variable, condition, rank, condition2))
        return self
    
    def absolute_rank(self, variable, condition, rank):
        assert isinstance(variable, ExperimentVariable)
        if variable not in self.rank_constraints:
            self.rank_constraints[variable] = len(self.constraints)
            self.constraints.append(AbsoluteRank(variable, condition, rank))
        else:
            pos = self.rank_constraints[variable]
            rank_constraint = self.constraints[pos]
            rank_constraint.add_rank(condition, rank)

        return self
    
    def extract_counterbalance_group(self, constraint):
        """Extract variables and condition count from a Counterbalance constraint."""
        var = constraint.get_variable()
        num_conditions = len(var)
        if isinstance(var, MultiFactVariable):
            return (var.get_variables(), num_conditions)
        return ([var], num_conditions)
    
    def _determine_num_plans(self):
  
        """Determine the number of experimental plans based on constraints and trial width."""
        if self.groups:
            return self.groups  # Assume already set

        counterbalanced_groups = []
        contains_ranked_var = False
        total_n_plans = 1

        for constraint in self.constraints:
            if isinstance(constraint, Counterbalance):
                group = self.extract_counterbalance_group(constraint)
                counterbalanced_groups.append(group)

            elif isinstance(constraint, AbsoluteRank):
                contains_ranked_var = True
                rank_counts = count_values(constraint.ranks)
                total_n_plans *= factorial_product_of_counts(rank_counts)

        for variables, num_conditions in counterbalanced_groups:
            num_trials = self.get_width()
            total_n_plans *= calculate_plan_multiplier(num_conditions, len(variables), num_trials)

        self.groups = Groups(int(total_n_plans) if (counterbalanced_groups or contains_ranked_var) else 0)
    
                


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

        # Handle between-subjects constraints
        for variable in self.bs_variables:
            self.constraints.append(
                InnerBlock(
                    variable,
                    width,
                    1
                )
            )
        
        # NOTE: ensure no downstream effects :)
        # self.designer.solver.all_different()
        self.designer.eval_constraints(self.constraints, self.groups, width)

    def test_eval(self):
        self._eval()
        return self.designer.eval_all()
        

    def eval(self):
        assert not self.is_empty
        self._eval()
        plans = self.designer.eval()
        self.plans = plans

    @property
    def counterbalanced(self):
        # FIXME: not handled for replicated trials
        return any(isinstance(c, Counterbalance) or isinstance(c, AbsoluteRank) for c in self.constraints)
    

    @property
    def is_empty(self):
        # FIXME: not handled for replicated trials
        return not self.variables 

        
    def counterbalance(self, variable, w = 0, h = 0, stride = [1, 1]):
        assert isinstance(variable, ExperimentVariable)
        

        width = self.get_width()

        self.constraints.append(Counterbalance(variable, width = w, height = h, stride = stride))
        return self
    
    def _new_ws_variables(self):
        if self.ws_variables:
            return self.ws_variables[0] if len(self.ws_variables) == 1 else multifact(self.ws_variables)
        else:
            return None

    def _new_bs_variables(self): 
        if self.bs_variables:   
            return self.bs_variables[0] if len(self.bs_variables) == 1 else multifact(self.bs_variables)
        else:
            return None
        
    def _combined_conditions(self, bs_conditions, ws_conditions):
        conditions = []
        if self.ws_variables and self.bs_variables:
            for i in range(len(bs_conditions)):
                conditions.append([bs_conditions[i][0] + "-" + ws_conditions[i][j] for j in range(len(ws_conditions[0]))])
        elif self.bs_variables:
            conditions = bs_conditions
        elif self.ws_variables:
            conditions = ws_conditions
        else:
            raise RuntimeError("No variables defined to generate conditions.")
        
        return conditions
        
    def random(self, n):
        assert len(self.ws_variables) or len(self.bs_variables) 

        ws_variable = self._new_ws_variables()
        ws_conditions = generate_conditions(n, ws_variable,self.get_width())

        
        bs_variable = self._new_bs_variables()
        bs_conditions = generate_conditions(n, bs_variable,1)
            
        return self._combined_conditions(bs_conditions, ws_conditions)
    

