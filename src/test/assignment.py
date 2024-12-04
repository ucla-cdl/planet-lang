from z3 import *
import numpy as np
from .narray import *


class Assignment:
    def __init__(self):
        self.units = None
        self.unit_options = None
        self.treatments = None
        self.unit_variables = []
        self.constraints = []

        self.test = False

    def compose_units(self, *argv):
        dims = [arg.n for arg in argv]
        self.unit_variables = [arg for arg in argv]

        matrix = add_dimension(dims, self.unit_variables)
        matrix = construct_units(matrix, dims)
        matrix = construct_z3(matrix, dims)

        self.units = matrix
      

    def compose_conditions(self, treatment):
        self.treatment = treatment
        symbols = len(treatment.conditions)
        r = len(self.units)
        c = len(self.units[0])
        if self.units != None:
            self.unit_options = [And(1 <= self.units[i][j], symbols >= self.units[i][j]) for i in range(r) for j in range(c)]


    # ensure that we distinguish this
    def recieve_different_conditions(self, block):
        r = self.unit_variables[0]
        c = self.unit_variables[1]
 
        for i in range(block.n):
            if block == r:
                arr = [self.units[i][j] for j in range(c.n)]
            if block == c:
                arr = [self.units[j][i] for j in range(r.n)]
             
            self.constraints.append(Distinct(arr))
        print(self.constraints)


    def generate(self):
        s = z3.Solver()
        s.add(self.unit_options + self.constraints)

        r = self.unit_variables[0].n
        c = self.unit_variables[1].n

        if (s.check() == sat):
            model = s.model()
            return np.matrix([[model[self.units[i][j]] for i in range(r)] for j in range(c)])

        
