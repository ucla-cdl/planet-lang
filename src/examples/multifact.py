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


des = (
    Design()
        .within_subjects(multifact([treatment, task]))
        .counterbalance(multifact([treatment, task]))
)

units = Units(12)

print(assign(units, des))