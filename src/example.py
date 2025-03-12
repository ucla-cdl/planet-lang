from z3 import *
from lib.groups import Groups
from lib.orders import Sequence
from lib.assignment import Assignment
from lib.variable import ExperimentVariable
from lib.blocks import BlockFactor
import math


class Design:
    def __init__(self):
        self.seq = None
        self.var = v
        self.groups = None

    
    def between_subjects(self, v):
        self.seq = Sequence(1)
        self.var = v
        return self

    def within_subjects(self, v):
        n = len(v)
        if isinstance(v, list):
            n = math.prod(list(map(len, v)))

        self.seq = Sequence(n)
        self.var = v
        return self
    
    def limit_groups(self, n):
        self.groups = Groups(n)
        return self
    
    def eval(self):
        assignment = Assignment()

        # participants.match(0,1, variable = task)
        # sequence.match(0,1, variable = task)
        # new Unit class

        if len(self.seq) > 3:
            assignment.test()

        if isinstance(self.var, list):
            assignment.assign(self.groups, self.seq, variables = self.var)
        else:
            assignment.assign(self.groups, self.seq, variables = [self.var])

        ret = assignment.eval()
        if len(self.seq) > 3:
            print(ret[[0, 3], :][:, [0, 3]])
        return ret
    
    def counterbalance(self):
        self.seq.all_different()
        return self
    
    def match_n(self, n):
        v = self.var[0]
        return self
    

    def __str__(self):
        return str(self.eval())

def nest(d1, d2):
    n = len(d1.var) * len(d2.var)
    des = Design().within_subjects([d1.var, d2.var]).counterbalance().limit_groups(n).match_n(3)
    return des



# save for later
# [[[0, 3], slice()], [slice(), [0, 3]]]








# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
treatment = ExperimentVariable(
    name = "treatment",
    options = ["A", "B", "c"]
)
task = ExperimentVariable(
    name = "task",
    options = ["A", "B"]
)

des1 = (
    Design()
        .within_subjects(treatment)
        .counterbalance()
        .limit_groups(3)
)

des2 = (
    Design()
        .within_subjects(task)
        .counterbalance()
        .limit_groups(2)
)


print(des1)
print(des2)

des = nest(des1, des2)

print(des)

