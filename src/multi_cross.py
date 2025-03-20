from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design


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


# # note: set / argv because no order
des = (
    Design()
        .within_subjects(treatment, task)
        .counterbalance(task, treatment)
        .num_trials(2)
)

print(des)