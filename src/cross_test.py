from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design, nest, cross


# NOTE: need to make all different wrt. variables. Should this be under the hood though?
# ie. handle with cross instead of reasoning about counterbalanced vars independently 
treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["A", "B"]
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
     
)

des2 = (Design()
        .within_subjects(test)
        .counterbalance(test)
)


final = cross(des, des2)

print(final)