from z3 import *
from lib.variable import ExperimentVariable, multifact
from lib.design import Design


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2"]
)


des = (
    Design()
        .within_subjects(multifact([treatment, task]))
        .counterbalance(multifact([treatment, task]))
)



print(des)