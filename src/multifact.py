from z3 import *
from lib.variable import ExperimentVariable
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
        .within_subjects(treatment, task)
        .counterbalance(task, treatment)
)



print(des)