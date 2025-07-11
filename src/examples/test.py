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
    options = ["1", "2", "3", "4"]
)


des = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
        .num_trials(2)
)

units = Units(8)
print(assign(units, des))