# External libraries
from z3 import *             # Requires: pip install z3-solver
import math
# Planet core modules (installed via `pip install -e .`)
from planet.variable import ExperimentVariable, MultiFactVariable, multifact
from planet.design import Design, Plans
from planet.unit import Groups
from planet.constraint import (
    Counterbalance
)


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
    