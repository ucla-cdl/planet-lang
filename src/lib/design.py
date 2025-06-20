from z3 import *
from lib.unit import Groups
from lib.orders import Sequence
from lib.candl import *
from lib.variable import MultiFactVariable, multifact
from .helpers import *
from .narray import *
from .candl import *
from .unit import Groups
from lib.constraint import StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock, Constraint, SetRank, SetPosition
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
    
    def get_plans(self, n=None):
        if self.plans is not None:
            return self.plans
        return self.eval() if self.counterbalanced else self.random(n or len(self.groups))
    
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

    # FIXME
    def eval(self, test = False):
        
        """
        Evaluate the experimental design and generate a solution.
        
        Returns:
            The evaluation result from the Assignment solver
        """

        # Get the width of the design
        width = self.get_width()
        sequence = Sequence(width)
        self.groups = self.groups or Groups(0)
        
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

        if test:
            self.plans = self.designer.eval_all()
        else:
            self.plans = self.designer.eval()

        return self.plans
        
    def counterbalance(self, variable, w = 0, h = 0, stride = [1, 1]):
        assert isinstance(variable, ExperimentVariable)

        self.counterbalanced = True

        if isinstance(variable, MultiFactVariable):
            variable = variable.variables
        else: 
            variable = [variable]

        width = 1
        for v in variable: 
            width *= len(v)

        # FIXME: should probably decouble this constraint block concept?
        self.constraints.append(NoRepeat([variable], width=width))
        self.constraints.append(Counterbalance(variable, width = w, height = h, stride = stride))
        return self
    
    def random(self, n):
        assert len(self.ws_variables) > 0 or len(self.bs_variables) > 0

        ws_variable = None
        bs_variable = None
        bs_conditions = None
        ws_conditions = None
        if len(self.ws_variables) > 0:
            ws_variable = self.ws_variables[0] if len(self.ws_variables) == 1 else multifact(self.ws_variables)
            ws_conditions = generate_conditions(n, ws_variable.conditions,self.get_width())
        if len(self.bs_variables) > 0:
            bs_variable = self.bs_variables[0] if len(self.bs_variables) == 1 else multifact(self.bs_variables)
            bs_conditions = generate_conditions(n, bs_variable.conditions,1)

        conditions = []
        if len(self.bs_variables) > 0 and len(self.ws_variables) > 0:
            for i in range(len(bs_conditions)):
                conditions.append([bs_conditions[i][0] + "-" + ws_conditions[i][j] for j in range(len(ws_conditions[0]))])
        elif len(self.bs_variables) > 0:
            conditions = bs_conditions
        elif len(self.ws_variables) > 0:
            conditions = ws_conditions
        else:
            print("err")
            
        return conditions
