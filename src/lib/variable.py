from z3 import *


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
            attr = options[i] if len(options) > 0 else "condition" + str(i)
            # instance of variable condition which represents a subcondition 
            # of this variable. Pass the current variable so the condition 
            # can refer back 
            self.conditions.append(attr)
            self.condition_map[attr] = i

    def get_condition(self, s):
        return self.conditions[self.condition_map[s]]

    def add_constraint(self, constraint):
        self.constraint = constraint

    def get_conditions(self):
        return self.conditions

    def __str__(self):
        return str(self.name)
    
    def __len__(self):
        return self.n
    

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
    
