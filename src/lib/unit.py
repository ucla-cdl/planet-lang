from z3 import *
from itertools import product
from collections import namedtuple
import random
import itertools


class Unit:
    """ a Unit represents a singular unit that participates in a study. Units
            get randomly assigned to an experimental group during assignment

    n: id of the unit
    """
    def __init__(self, n):
        self.n = n
        self.vars = {}


class Units:
    def __init__(self, n):
        self.units = [Unit(i) for i in range(n)]
       



        
    
