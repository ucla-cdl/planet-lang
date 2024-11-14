from z3 import *


class Constraint:
    def __init__(self, variable):
        self.variable = variable

    def get_variable(self):
        return self.variable
    


# NOTE: this should be a superclass of Match, Any, and Different 
# this class only adds one Z3 var to the solver
# because it must be exactly this subcondition
class TwoElemConstraint(Constraint):
    def __init__(self, i1, i2, variables):
        Constraint.__init__(self, variables)
        if not isinstance(variables, list):
            variables = [variables]
        self.variables = variables
        self.index_to_match = i1
        self.index = i2
    
    def get_index_to_match(self):
        return self.index_to_match
    
    def get_index(self):
        return self.index



# this is a z3 class wrapper 
# note: we probably want to store the proper z3
# eval here... condition is the condition that we 
# derive a different subcondition from
# example: condition passed is an ffl condition,
# so this wrapper indicates that the condition it appplies to 
# is not an ffl condition (so in this case, it must be latex)

class Different(TwoElemConstraint):
    """
    this is what we want in the sequence class: 
        self.solver.add(
            self.z3_vectors[variable][i1] != self.z3_vectors[variable][i2]
        )

        key information: which variable, which index in order
    """
    def __init__(self, i1, i2, variables = []):
        TwoElemConstraint.__init__(self, i1, i2, variables)

    def eval_constraint(self, z3_variable_map):
        ret = []
        for row in z3_variable_map[self.variables[0]]:
            ret.append(row[self.index_to_match] != row[self.index])
        return ret


class AllDifferent(Constraint):
    def __init__(self, variable):
        self.reference_variable = variable

    def get_reference_block(self):
        return self.reference_variable

    

# z3 class wrapper. Same concept as above, but 
# instead of creating a Not object, we copy 
# the exact same constraints from condition 
# to add to the new condition's solver
class Match(TwoElemConstraint):
    def __init__(self, i1, i2, variables):
        TwoElemConstraint.__init__(self, i1, i2, variables)

    def eval_constraint(self, z3_variable_map):
        ret = []
        for row in z3_variable_map[self.variables[0]]:
            ret.append(row[self.index_to_match] == row[self.index])
        return ret

# given a variable, create an z3 instance that allows
# us to choose any of the subcondiiton options
# example: given treatment, then we can allow ffl OR latex
class Force(Constraint):
    def __init__(self, variable, condition, i):
        Constraint.__init__(self, variable)
        self.condition = condition
        self.i = i

    def get_condition(self):
        return self.condition
    
    def get_index(self):
        return self.i
    
    def eval_constraint(self, z3_variable_map):
        ret = []
        for row in z3_variable_map[self.variable]:
            ret.append(row[self.i] == self.condition)
        return ret

 