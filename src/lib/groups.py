from .blocks import BlockFactor


# inherit from variable? 
class Groups(BlockFactor):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n, labels = None):
        BlockFactor.__init__(self, [i for i in range(n)])
        self.n = n
        self.labels = labels

    def expand_groups(self, num_groups):
        assert num_groups % self.n == 0
        return Groups(self.n)
