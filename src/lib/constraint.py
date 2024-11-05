from z3 import *


class Constraint:
    def __init__(self, var):
        self.var = var
        self.test = None


# NOTE: this should be a superclass of Match, Any, and Different 
# this class only adds one Z3 var to the solver
# because it must be exactly this subcondition
class Exact(Constraint):
    def __init__(self, var, condition):
        self.__z3__ = var.name_to_condition[condition].__z3__
        Constraint.__init__(self, var)

    def __str__(self):
        return "must be: " + str(self.__z3__)

# this is a z3 class wrapper 
# note: we probably want to store the proper z3
# eval here... condition is the condition that we 
# derive a different subcondition from
# example: condition passed is an ffl condition,
# so this wrapper indicates that the condition it appplies to 
# is not an ffl condition (so in this case, it must be latex)
class Different(Constraint):
    def __init__(self, var, condition):
        self.condition = condition
        self.__z3__ = condition.var_to_z3[var].__z3__
        # somewhere we should note that there 
        # is a dependency on condition and we cant eval 
        # until we eval the previous condition
        # should we force eval in this case?

        Constraint.__init__(self, var)

    def __str__(self):
        return "not " + "eval of condition: " + "(" + str(self._z3_options) + ")"
    

# z3 class wrapper. Same concept as above, but 
# instead of creating a Not object, we copy 
# the exact same constraints from condition 
# to add to the new condition's solver
class Match(Constraint):
    def __init__(self, var, condition):
        self.condition = condition
        self.__z3__ = condition.var_to_z3[var].__z3__
        # somewhere we should note that there 
        # is a dependency on condition and we cant eval 
        # until we eval the previous condition
        # should we force eval in this case?

        Constraint.__init__(self, var)

    def __str__(self):
        return "eval of condition: " + "(" + str(self._z3_options) + ")"

# given a variable, create an z3 instance that allows
# us to choose any of the subcondiiton options
# example: given treatment, then we can allow ffl OR latex
class Any(Constraint):
    def __init__(self, var):
        self.__z3__ = Or([option.__z3__ for option in var.conditions])
        Constraint.__init__(self, var)

    def __str__(self): 
        return "any of: " + str([option.__z3__ for option in self.var.conditions])