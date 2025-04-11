from .blocks import BlockFactor  
from .constraint import AllMatch, Majority

class Members(BlockFactor):
    def __init__(self, n):
        BlockFactor.__init__(self, [f"m{i+1}" for i in range(n)])
        self.n = n

    def all_match(self, variable, wrt = None, level=None):
        constraint = AllMatch(variable, wrt = wrt, level = level)
        self.constraints.append(constraint)

    def majority(self, i, val, dim, variable):
        """
        i: level of block factor
        val: which attr
        dim: which block factor 
        """
        constraint = Majority(i, val, dim, variable)
        self.constraints.append(constraint)