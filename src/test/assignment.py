from z3 import *
import numpy as np

class Assignment:
    def __init__(self):
        self.units = None
        self.unit_options = None
        self.treatments = None

        self.unit_variables = []

        self.constraints = []

    def compose_units(self, participants, sequence):
        r = participants.n
        c = sequence.n

        self.unit_variables.append(participants)
        self.unit_variables.append(sequence)

        self.units = [[Int(f"unit_{i+1}{j+1}") for i in range(r)] for j in range(c)]

    def compose_conditions(self, treatment):
        self.treatment = treatment
        symbols = len(treatment.conditions)
        r = len(self.units)
        c = len(self.units[0])
        if self.units != None:
            self.unit_options = [And(1 <= self.units[i][j], symbols >= self.units[i][j]) for i in range(r) for j in range(c)]

    def recieve_different_conditions(self, block):
        r = self.unit_variables[0]
        c = self.unit_variables[1]


        for i in range(r.n):
            if block == r:
                self.constraints.append(Distinct([self.units[i][j] for j in range(c.n)]))
            elif block == c:
                self.constraints.append(Distinct([self.units[j][i] for j in range(c.n)]))


    def generate(self):
        s = z3.Solver()
        s.add(self.unit_options + self.constraints)

        r = self.unit_variables[1].n
        c = self.unit_variables[0].n

        if (s.check() == sat):
            model = s.model()
            return np.matrix([[model[self.units[i][j]] for i in range(r)] for j in range(c)])

        
