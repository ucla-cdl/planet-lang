from z3 import *
from .variable import ExperimentVariable

class BlockFactor(ExperimentVariable):
    def __init__(self, levels, name = ""):
        if name == "":
            name = self.__class__
        ExperimentVariable.__init__(self, name, num_options=len(levels), options = levels)
        self.n = len(levels)
        self.levels = levels
        self.sequence_length = self.n 
        self.solver = z3.Solver()
        self.constraints = []
        self.z3_vectors = None # rep each var in z3
        self.all_orders = [] # stores all possible orders given constraint

    def __len__(self):
        return self.n


class Block: 
    def __init__(self, variable, assignment):
        self.variable = variable
        self.designer = assignment
