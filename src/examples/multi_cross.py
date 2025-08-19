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
        .within_subjects(treatment, task, test, test2)
        .counterbalance(task, treatment)
        .counterbalance(test, test2)
        .num_trials(4)
        .limit_plans(8)
)

des.eval()
# print(des)