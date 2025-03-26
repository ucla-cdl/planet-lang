from z3 import *
from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest


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
        .within_subjects(multifact([treatment, task]))
        .counterbalance(task)
        .counterbalance(treatment)
        .num_trials(2)
     
)

des3 = (Design()
        .within_subjects(test)
        .counterbalance(test)
        .limit_groups(2)
)

des4 = (Design()
        .within_subjects(test2)
        .counterbalance(test2)
        .limit_groups(2)
)

d2 = nest(des3, des)

d5 = nest(d2, des4)

print(d5)