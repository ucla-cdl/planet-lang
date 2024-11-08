# I think I can get rid of this class

from z3 import *
from.variable import VariableCondition

# Condition represents one possible "total condition" 
# pass in metaconditions to construct Condition, 
# along with constraints on the condition
class ExperimentCondition():
    # argv consists of Variable types
    def __init__(self, name, *argv):

        for arg in argv:
            assert isinstance(arg, VariableCondition)

        self.variable_conditions = argv
        self.name = str(tuple(v_condition.name for v_condition in self.variable_conditions))
                
  
    def __str__(self):
        return str(self.name)


class ConditionTest:
    def __init__(self, *argv):
    

        self.name = __class__

    def add_name(self, name):
        self.name = name

    def __str__(self):
        return str(self.name)
    

