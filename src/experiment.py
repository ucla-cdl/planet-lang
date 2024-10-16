from z3 import *
from itertools import product
from collections import namedtuple
import random
import itertools

# Condition represents one possible "total condition" 
# pass in metaconditions to construct Condition, 
# along with constraints on the condition
class ExperimentCondition():
    # argv cinsists of Variable types
    def __init__(self, *argv):
        self.var_to_z3 = {} # dict stores var to the constrained options 
        for arg in argv:
            # arg is a Z3Var type with Different, or Match wrapper 
            # arg.var is a and instance of a Variable object
            self.var_to_z3[arg.var] = arg

        # probably change this name... stores what we need 
        # to add to the solver based on the constraints
        # but we add to the solver in condition order...
        self.__z3__ = []
     


    # change this from eval to a solver constructor 
    # call equivilant in constructor 
    def eval(self):

        # the way we represent each class in z3 is different
        # based on class wrapper... # check if instance and then 
        # append proper Z3 class based on variables

    

        # messy messy code :(
        for var in self.var_to_z3:
            if isinstance(self.var_to_z3[var], Any):
                self.__z3__.append(self.var_to_z3[var].__z3__)
                s = z3.Solver()
                s.add(self.var_to_z3[var].__z3__)
                if s.check() == sat:
                    m = s.model()
                self.var_to_z3[var].test = m
            if isinstance(self.var_to_z3[var], Exact):
                self.__z3__.append(self.var_to_z3[var].__z3__)
                self.var_to_z3[var].test = solve(self.var_to_z3[var].__z3__)
            if isinstance(self.var_to_z3[var], Different):
                print("here")
                # left off here: need to get the evaluated model
                # and make sure that the values do not reflect this 
                print(self.var_to_z3[var].condition.var_to_z3[var], self.var_to_z3[var].condition.var_to_z3[var].test)
                self.__z3__.append((self.var_to_z3[var].condition.var_to_z3[var].__z3__))
            if isinstance(self.var_to_z3[var], Match):
    
                print("here", self.var_to_z3[var].condition.var_to_z3[var].test)
                self.__z3__.append((self.var_to_z3[var].condition.var_to_z3[var].__z3__))
                

        
       

        return self.__z3__

  
    def __str__(self):
        return " ".join(str(key) + ": " + str(self.var_to_z3[key]) for key in self.var_to_z3)
    

# NOTE: this should be a superclass of Match, Any, and Different 
# this class only adds one Z3 var to the solver
# because it must be exactly this subcondition
class Exact:
    def __init__(self, var, option):
        self.var = var
        self.__z3__ = var.name_to_condition[option].__z3__
        self.test = None

    def __str__(self):
        return "must be: " + str(self.__z3__)

# this is a z3 class wrapper 
# note: we probably want to store the proper z3
# eval here... condition is the condition that we 
# derive a different subcondition from
# example: condition passed is an ffl condition,
# so this wrapper indicates that the condition it appplies to 
# is not an ffl condition (so in this case, it must be latex)
class Different:
    def __init__(self, var, condition):
        self.var = var
        self.condition = condition
        self._z3_options = condition.var_to_z3[var]
        self.__z3__ = self._z3_options.__z3__
        self.test = None
        # somewhere we should note that there 
        # is a dependency on condition and we cant eval 
        # until we eval the previous condition
        # should we force eval in this case?

    def __str__(self):
        return "not " + "eval of condition: " + "(" + str(self._z3_options) + ")"
    

# z3 class wrapper. Same concept as above, but 
# instead of creating a Not object, we copy 
# the exact same constraints from condition 
# to add to the new condition's solver
class Match:
    def __init__(self, var, condition):
        self.var = var
        self.condition = condition
        self._z3_options = condition.var_to_z3[var]
        self.__z3__ = self._z3_options.__z3__
        # somewhere we should note that there 
        # is a dependency on condition and we cant eval 
        # until we eval the previous condition
        # should we force eval in this case?

    def __str__(self):
        return "eval of condition: " + "(" + str(self._z3_options) + ")"

# given a variable, create an z3 instance that allows
# us to choose any of the subcondiiton options
# example: given treatment, then we can allow ffl OR latex
class Any:
    def __init__(self, var):
        self.var = var
        self.__z3__ = Or([option.__z3__ for option in var.conditions])

    def __str__(self): 
        return "any " + str(self.__z3__)


# This is a variable class that stores experimental
# variables and their respective options 
# based on user definition
class ExperimentVariable:
    def __init__(self, name, num_options, options = []):
        # should we use argv or kwargs in place of a list?
        assert num_options == len(options) or len(options) == 0


        self.name = name
        self.n = num_options
        # some way to remove the need for both 
        self.conditions = []
        self.name_to_condition = {}

        for i in range(num_options):
            # create a name for the condition if the user 
            # left it unnamed 
            attr = options[i] if len(options) > 0 else "condition" + str(i)
            # instance of option class which represents a subcondition 
            # of this variable. Pass the current variable so the condition 
            # can refer back 
            option = VariableCondition(attr, self)

            # these are both methods for tracking the conditions
            self.conditions.append(option)
            setattr(self, attr, option) # unused at the moment 

        # this is kind of silly... there should be a better way to reference this ?
        for condition in self.conditions:
            self.name_to_condition[condition.name] = condition



    # these should all return lists of variable options (defined by user)
    # not in use: does not utilize z3 but randomly picks one 
    def any_option(self):
        return self.conditions[random.randint(0, self.n-1)]
    
    # in use: returns an instance of an Any object 
    def any_test(self):
        return Any(self)
    
    # not in use...
    def match(self, condition):
        return condition.get_option(self)

    # in use: returns instance of match object
    # note to self: do we want to return these 
    # z3 variable wrappers (ie. match) from variable?
    def match_test(self, condition):
        return Match(self, condition)
    
    # not in use. returns all conditions minus the one 
    # used by the specified condition
    def different(self, condition):
        options = []
        for option in self.conditions:
            if option != condition.var_to_option[self]:
                options.append(option)
      
        return options[random.randint(0, len(options)-1)]

    # in use: returns different wrapper since we don't know the eval yet
    def different_test(self, condition):
        return Different(self, condition)

    # not in use
    def get_option(self, option):
        return self.name_to_condition[option]
    
    # returns z3 wrapper 
    def get_test(self, option):
        return Exact(self, option)

    def __str__(self):
        return self.name


class VariableCondition:
    def __init__(self, name, var):
        self.var = var # refer back to var object that constructed this option
        self.name = name
        self.__z3__ = Bool(name) # should we keep this here? what other properties?

    def __str__(self):
        return "option: " + self.name + " from variable: " + self.var.name 
    

class ConditionOrder:
    def __init__(self, n):
        # this is how many conditions the 
        # unit sees during the experiment
        self.n = n
        self.conditions = [None for i in range(n)]
        self.curr = 0

    # how we add to order 
    def next(self, condition):
        assert self.curr < self.n
        self.conditions[self.curr] = condition
        self.curr += 1

    # dont construct until called next self.n times
    def eval(self):
        s = z3.Solver()
        for condition in conditions:
            s.push()
            s.add(condition.eval())
            print(s)
            s.pop()

# number of units in experiment
# should the assignment object create groups and units 
class Unit:
    def __init__(self, n):
        self.n = n

class Assignment:
    def __init__(self, variables, units, conditions_per_unit = 1, order_conditions = None):
        self.combinations = list(itertools.product(*[v.conditions for v in variables]))
        if order_conditions is None:
            variable_conditions = [Any(var) for var in variables]
            self.order_conditions = ExperimentCondition(*variable_conditions)
        else:
            self.order_conditions = order_conditions

        self.conditions_per_unit = conditions_per_unit
        self.units = units
        self.variables = variables

    def assign_unit(self, n):
        unit = self.units[n]
        for condition in self.order_conditions:
            condition.eval()

            

        

# should these be user-created subclasses?
treatment = ExperimentVariable(
    name = "treatment",
    num_options = 2,
    options = ["ffl", "latex"]
)
task = ExperimentVariable(
    name = "task",
    num_options = 2,
    options = ["editing", "creation"]
)

# should we instead pass the variables
# and then place the constraints
c1 = ExperimentCondition(
    treatment.any_test(),
    task.get_test("creation")
)
c2 = ExperimentCondition(
    treatment.different_test(c1), # alt = condition1.different(treatment)
    task.get_test("creation") 
)
c3 = ExperimentCondition(
    treatment.match_test(c1), # alt = condition1.match(treatment)
    task.get_test("editing")
)
c4 = ExperimentCondition(
    treatment.match_test(c2), # alt = condition2.match(treatment)
    task.get_test("editing")
)

# something with total conditions here? treatment x task 
order = [c1, c2, c3, c4]
units = []
for i in range(20):
    units.append(Unit(i))

assignment = Assignment(variables = [treatment, task],
                        units = units,
                        conditions_per_unit = 4,
                        order_conditions = order,
            )

assignment.assign_unit(1)








