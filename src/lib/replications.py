from .variable import ExperimentVariable
from .design import Design
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
from lib.design import Plans
from lib.candl import generate_conditions
import math
import pandas as pd


class Replications(Plans):
    """Main class for creating experimental designs."""
    def __init__(self, n):
        super().__init__()
        var = ExperimentVariable("replications", 1)
        self._add_variable(var)
        self.groups = Groups(1)
        self.num_trials(n)
        self.constraints.append(Counterbalance(var, width = n, height = 1, stride = [1,1]))

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
    
    
    def get_width(self):
        return self.trials or math.prod(v.n for v in self.ws_variables)
    