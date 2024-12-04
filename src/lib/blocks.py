from z3 import *
from .constraint import Different, Match, Force, AllDifferent
from .variable import ExperimentVariable

class BlockFactor(ExperimentVariable):
    def __init__(self, levels):
        ExperimentVariable.__init__(self, self.__class__, num_options=len(levels), options = levels)
        self.n = len(levels)
        self.levels = levels
        self.sequence_length = self.n 
        self.solver = z3.Solver()
        self.constraints = []
        self.z3_vectors = None # rep each var in z3
        self.all_orders = [] # stores all possible orders given constraint

    def different(self, i1, i2, variable):

        assert i1 <= self.n and i2 <= self.n

        constraint = Different(i1, i2, variable)
        self.constraints.append(constraint)

    def match(self, i1, i2, variable):

        assert i1 <= self.n and i2 <= self.n

        constraint = Match(i1, i2, variable)
        self.constraints.append(constraint)


    # not finished (need a mapping of indices to variable assignments)
    def force(self, i, variable, condition):
        assert i <= self.n 

        val = 0

        # probably somethign more efficient... do we want to store 
        # these mappings, so we dont have to comput every time and then loop?
        # reasoning not to is that no variable should have many conditions
        condition_names = list(map(lambda condition: condition.name, variable.conditions))
   
        val = condition_names.index(condition) + 1
        constraint = Force(variable, val, i)
        self.constraints.append(constraint)

    def all_different(self):
        constraint = AllDifferent(self)
        self.constraints.append(constraint)

    def __len__(self):
        return self.n


class Block: 
    def __init__(self, variable, assignment):
        self.variable = variable
        self.assignment = assignment
