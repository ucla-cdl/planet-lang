from z3 import *
from .constraint import Different, Match, Constraint, Force, AllDifferent

class BlockFactor:
    def __init__(self, levels):
        self.n = len(levels)
        self.blocks = [Block(self, level) for level in levels]

        self.sequence_length = self.n 
        self.solver = z3.Solver()

        self.constraints = []


        self.z3_vectors = None # rep each var in z3


        self.all_orders = [] # stores all possible orders given constraint

    def eval_constraint(self, constraint):

        assert isinstance(constraint, Constraint)

        if isinstance(constraint, Different) or isinstance(constraint, Match):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

        if isinstance(constraint, Different):
            self.solver.add(self.z3_vectors[var][i1] != self.z3_vectors[var][i2])
        if isinstance(constraint, Match):
            self.solver.add(self.z3_vectors[var][i1] == self.z3_vectors[var][i2])
        if isinstance(constraint, Force):
            variable = constraint.get_variable()
            val = constraint.get_condition()
            i = constraint.get_index()
            self.solver.add(self.z3_vectors[variable][i] == val)

    def different(self, i1, i2, variable):
        constraint = Different(i1, i2, variable)
        self.constraints.append(constraint)

    def match(self, i1, i2, variable):
        constraint = Match(i1, i2, variable)
        self.constraints.append(constraint)


    # not finished (need a mapping of indices to variable assignments)
    def force(self, i, variable, condition):
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


class Block: 
    def __init__(self, variable, assignment):
        self.variable = variable
        self.assignment = assignment
