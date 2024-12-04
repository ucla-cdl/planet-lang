
from z3 import *

from .blocks import BlockFactor

class Sequence(BlockFactor):
    """The PossibleOrders class represents all of the possible
        orders of conditions in an experiment, where each order
        is an experimental group

    n: the number of conditions in each order
    we use argv so the user can pass any number of variables
    because experiments have varying amount of variables
    """
    def __init__(self, n, *argv):

        BlockFactor.__init__(self, [i for i in range(n)])

       


    
    







    
