from .blocks import BlockFactor


# inherit from variable? 
class Participants(BlockFactor):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n=0):
        BlockFactor.__init__(self, [f"p{i+1}" for i in range(n)])
        self.n = n
        self.attributes = []

    def add_attribute(self, attr):

        assert isinstance(attr, BlockFactor)
        self.attributes.append(attr)
