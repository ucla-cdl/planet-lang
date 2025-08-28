from z3 import *
from functools import reduce
import itertools


class ExperimentVariable:
    """The Experiment Variable represents a user-defined factor or characteristic 
            that changes throughout the course of an experiment.

    name: user-defined name of the variable
    num_options: how many conditions we can assign to the variable
    possible_orders: list of possible assignment values
    """
     
    def __init__(self, name, num_options=0, options = []):
        # should we use argv or kwargs in place of a list?

        assert len(options) > 0 or num_options > 0

        num_options = len(options) if num_options == 0 else num_options

        assert num_options == len(options) or len(options) == 0
        assert num_options > 0

        self.name = name
        self.constraint = None
        self.n = num_options

        # experiment variables holds metadata, and information about 
        # possible assignments (ie. the conditions)
        self.conditions = []
        self.condition_map = dict()
        for i in range(num_options):
            # create a name for the condition if not defined
            attr = options[i] if len(options) > 0 else str(i)
            # instance of variable condition which represents a subcondition 
            # of this variable. Pass the current variable so the condition 
            # can refer back 
            self.conditions.append(attr)
            self.condition_map[attr] = i

    def get_condition(self, s):
        return self.conditions[self.condition_map[s]]

    def get_variables(self):
        return [self]

    def add_constraint(self, constraint):
        self.constraint = constraint

    def get_conditions(self):
        return self.conditions

    def __str__(self):
        return str(self.name)
    
    def __len__(self):
        return self.n
    
class DesignVariable:
    def __init__(self, var):
        assert isinstance(var, ExperimentVariable)
        self.var = var
        self.counterbalanced = False
        self.within_subjects = False

    def is_within_subjects(self, flag = True):
        self.within_subjects = flag

    def counterbalance(self, flag = True):
        self.counterbalanced = flag

   






class Replications(ExperimentVariable):
    def __init__(self, n):
        self.__init__("replications", n)

class MultiFactVariable(ExperimentVariable):
    def __init__(self, variables):
        self.n = reduce(lambda x, y: x*y, list(map(len, variables)))
        combinations = list(itertools.product(*[variable.conditions for variable in variables]))
        combinations = ["-".join(combination) for combination in combinations]

        super().__init__("factorial", self.n, options = combinations)
        self.variables = variables

    def _get_variables(self):
        return self.variables

    def _unpack_variables(self, variables):
        if len(variables) == 1:
            return variables[0]._get_variables() if isinstance(variables[0], MultiFactVariable) else variables

        else:
            curr = variables[0]
            arr = curr._get_variables() if isinstance(curr, MultiFactVariable) else [curr]
            tail = self._unpack_variables(variables[1:])
            arr.extend(self._unpack_variables(variables[1:]))
            return arr

    def get_variables(self):
        return self._unpack_variables(self.variables)
    
    def contains_variable(self, var):
        return var in self.variables
    
    def get_variables(self):
        return self.variables
    

def multifact(variables):
    return MultiFactVariable(variables)

class BaseVariable(ExperimentVariable):
    def __init__(self):
        super().__init__("base", 1)


class VariableCondition:
    """The Variable represents a value that a user can assign to 
            a specific condition.

    NOTE: the ExperimentVariable() class is composed of VariableConditions
            - the user does not create these 

    name: user-defined name of the condition
    var: variable that this condition gets assigned to
             (the variable and condition can reference each-other)
    """
    def __init__(self, name, var):
        self.var = var # refer back to var object that constructed this option
        self.name = name

    def __str__(self):
        return self.name 
    
class UnitVariable:
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels
    
