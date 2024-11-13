from .blocks import BlockFactor


class Participants(BlockFactor):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n):
        BlockFactor.__init__(self, [i for i in range(n)])
        self.n = n
