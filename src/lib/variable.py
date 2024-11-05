from z3 import *
from itertools import product
from collections import namedtuple
import random
import itertools
from .constraint import Any, Exact, Match, Different


class ExperimentVariable:
    """The Experiment Variable represents a user-defined factor or characteristic 
            that changes throughout the course of an experiment.

    name: user-defined name of the variable
    num_options: how many conditions we can assign to the variable
    possible_orders: list of possible assignment values
    """
     
    def __init__(self, name, num_options=0, options = []):
        # should we use argv or kwargs in place of a list?
        if num_options == 0:
            num_options = len(options)

        assert num_options == len(options) or len(options) == 0
        assert num_options > 0

        self.name = name
        self.n = num_options

        # we definitely do not need both 
        self.conditions = []
        self.name_to_condition = {}

        for i in range(num_options):
            # create a name for the condition if not defined
            attr = options[i] if len(options) > 0 else "condition" + str(i)
            # instance of variable condition which represents a subcondition 
            # of this variable. Pass the current variable so the condition 
            # can refer back 
            option = VariableCondition(attr, self)

            # these are both methods for tracking the conditions
            self.conditions.append(option)

        # this is kind of silly... there should be a better way to reference this ?
        for condition in self.conditions:
            self.name_to_condition[condition.name] = condition

    # in use: returns an instance of an Any object 
    def any(self):
        return Any(self)

    # in use: returns instance of match object
    # note to self: do we want to return these 
    # z3 variable wrappers (ie. match) from variable?
    def match(self, condition):
        return Match(self, condition)

    # in use: returns different wrapper since we don't know the eval yet
    def different(self, condition):
        return Different(self, condition)
    
    # returns z3 wrapper 
    def get(self, option):
        return Exact(self, option)

    def __str__(self):
        return str(self.name)
    

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
        self.__z3__ = Bool(name) # should we keep this here? what other properties?

    def __str__(self):
        return self.name 
    
class UnitVariable:
    def __init__(self, name, levels):
        self.name = name
        self.levels = levels
    
