from z3 import *
from .blocks import BlockFactor
from .constraint import OccurNTimes


class Unit:
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n):
        self.n = n

class Units(BlockFactor):
    def __init__(self, n):
        BlockFactor.__init__(self, [str(i) for i in range(n)])
        self.n = n
        self.attributes = []

    def add_attribute(self, attr):

        assert isinstance(attr, BlockFactor)
        self.attributes.append(attr)


    def occurs_n_times(self, n):
        constraint = OccurNTimes(n, self)
        self.constraints.append(constraint)
       

# inherit from variable? 
class Participants(Units):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n=0):
        Units.__init__(self, n)

# inherit from variable? 
class Groups(Units):
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n, labels = None):
        Units.__init__(self, n)
        self.groups = [Group(i) for i in range(n)]

    def expand_groups(self, num_groups):
        assert num_groups % self.n == 0
        return Groups(num_groups)


class Group:
    def __init__(self, n):
        self.n = n
        self.labels = []

    def add_label(self, label):
        self.labels.append(label)

    



        
    
