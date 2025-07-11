from z3 import *
from lib.unit import Groups
from lib.orders import Sequence
from lib.candl import *
from lib.variable import MultiFactVariable, multifact
from .helpers import *
from .narray import *
from .candl import *
from .unit import Groups
from lib.constraint import StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock, Constraint, SetRank, SetPosition, AbsoluteRank
from lib.designer import Designer
from lib.candl import generate_conditions
import math
import pandas as pd

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
        self.counterbalanced = False
        self.plans = None

class Design(Plans):
    """Main class for creating experimental designs."""
    def __init__(self):
        super().__init__()
        self.rank_constraints = {}
  
    def to_latex(self):
        matrix = self.eval()
        trials = [f"trial{i+1}" for i in range(len(matrix[0]))]
        df = pd.DataFrame(matrix, columns=trials)

        try:
            filepath = "../outputs/design.tex"
            create_directory_for_file(filepath)
            with open(filepath, 'w', encoding='utf-8') as tex_file:
                tex_file.write(df.to_latex())
            print(f"success")
        except Exception as e:
            print(f"An error occurred: {e}")

    def num_trials(self, n):
        self.trials = n
        return self
    
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
        return self
    
    def limit_groups(self, n):
        self.groups = Groups(n)
        return self
    
    def is_random(self):
        return not self.counterbalanced
    
    def get_plans(self):
        if self.plans is not None:
            return self.plans
        return self.eval()
    
    
    def get_width(self):
        return self.trials or math.prod(v.n for v in self.ws_variables)
    
    def start_with(self, variable, condition):
        assert isinstance(variable, ExperimentVariable)
        self.constraints.append(StartWith(variable, condition))
        return self
    
    def set_position(self, variable, condition, pos):
        assert isinstance(variable, ExperimentVariable)
        self.counterbalanced = True
        self.constraints.append(SetPosition(variable, condition, pos))
        return self
    
    def set_rank(self, variable, condition, rank, condition2):
        assert isinstance(variable, ExperimentVariable)
        self.counterbalanced = True
        self.constraints.append(SetRank(variable, condition, rank, condition2))
        return self
    
    def absolute_rank(self, variable, condition, rank):
        assert isinstance(variable, ExperimentVariable)
        if variable not in self.rank_constraints:
            self.counterbalanced = True
            self.rank_constraints[variable] = len(self.constraints)
            self.constraints.append(AbsoluteRank(variable, condition, rank))
        else:
            pos = self.rank_constraints[variable]
            rank_constraint = self.constraints[pos]
            rank_constraint.add_rank(condition, rank)

        return self
    
    def _determine_num_plans(self):
        if not self.groups:
            counterbalanced_groups = []
            for constraint in self.constraints:
                if isinstance(constraint, Counterbalance):
                    counterbalanced_variable = constraint.get_variable()
                    if isinstance(counterbalanced_variable, MultiFactVariable):
                        counterbalanced_groups.append((counterbalanced_variable.get_variables(), len(counterbalanced_variable)))
                    else:
                        counterbalanced_groups.append(([counterbalanced_variable], len(counterbalanced_variable)))

            total_n_plans = 1
            for group in counterbalanced_groups:
                num_trials = self.get_width()
                if num_trials > group[1]:
                    num_repeats = int(self.get_width()/group[1])
                    total_n_plans *= math.factorial(group[1]) / math.prod(math.factorial(num_repeats) for _ in group[0])
                elif num_trials < group[1]:
                    total_n_plans *= math.factorial(group[1]) / math.factorial(group[1] - num_trials)
                else: 
                    total_n_plans *= math.factorial(group[1])
            if counterbalanced_groups:
                self.groups = Groups(int(total_n_plans))
            else:
                self.groups = Groups(0)
            


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
          
        self.designer.solver.all_different()
        self.designer.eval_constraints(self.constraints, self.groups, width)

    def test_eval(self):
        self._eval()
        return self.designer.eval_all()
        

    def eval(self):
        self._eval()
        return self.designer.eval()

        
    def counterbalance(self, variable, w = 0, h = 0, stride = [1, 1]):
        assert isinstance(variable, ExperimentVariable)
     
        # FIXME: this flag is awful. How to circumvent this? 
        self.counterbalanced = True
        
        if isinstance(variable, MultiFactVariable):
            variables = variable.get_variables()
        else:
            variables = [variable]

        width = 1
        for v in variables: 
            width *= len(v)

        # FIXME: should probably decouble this constraint block concept?
        self.constraints.append(NoRepeat(variable, width=width))
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
    

