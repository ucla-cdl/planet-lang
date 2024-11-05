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
        self.blocks = {}

    def block(self, variable, split):
        assert split*len(variable.levels) == 1
        for level in variable.levels:
            self.blocks[level] = []

        for unit in self.units:
            self.blocks[variable.levels[random.randint(0,1)]].append(unit)


    def assign(self, groups):
        groups = groups.eval()
        for block in self.blocks: 
            print(block)
            for unit in self.blocks[block]: 
                print("unit " + str(unit.n), "group " + str(groups[random.randint(0, len(groups)-1)]))


        print(groups)

        
    
