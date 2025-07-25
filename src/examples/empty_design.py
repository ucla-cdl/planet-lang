import sys
sys.path.append("../")
from z3 import *
from lib.replications import Replications
from lib.variable import ExperimentVariable, multifact
from lib.nest import nest
from lib.design import Design
from lib.assignment import assign, assign_counterbalance
from lib.unit import Units



x = ExperimentVariable(
    name = "x",
    options = ["a", "b"] 
)
units = Units(24)
des = (
    Design()
        .within_subjects(x)
        .counterbalance(x)
)
block = (
    Design()
        .num_trials(2)
)


final = nest(inner=block, outer=des)
assignment = assign(units, final)
print(assignment)
