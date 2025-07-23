import sys
sys.path.append("../")

from z3 import *
from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.assignment import assign
from lib.unit import Units


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2"]
)


combine = multifact([treatment, task])

des = (
    Design()
        .within_subjects(treatment)
        .within_subjects(task)
        .counterbalance(combine)
        .limit_groups(4)
)

units = Units(12)

print(assign(units, des))