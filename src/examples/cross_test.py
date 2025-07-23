import sys
sys.path.append("../")

from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.nest import cross, nest
from lib.unit import Units
from lib.assignment import assign


# NOTE: need to make all different wrt. variables. Should this be under the hood though?
# ie. handle with cross instead of reasoning about counterbalanced vars independently 
treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["A", "B", "C", "D"]
)

test = ExperimentVariable(
    name = "test",
    options = ["x", "y"]
)

test2 = ExperimentVariable(
    name = "test2",
    options = ["X", "Y"]
)


# # note: set / argv because no order
des = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
        .limit_groups(4)
     
)

des2 = (Design()
        .within_subjects(test)
        .counterbalance(test)
)

des3 = (Design()
        .within_subjects(test2)
        .counterbalance(test2)
)

intermediate = nest(inner=des3, outer=des2)

units = Units(4)

final = cross(des, intermediate)
print(assign(units, final))

