from z3 import *
import sys

sys.path.append("../")
from lib.assignment import assign
from lib.unit import Units
from lib.variable import ExperimentVariable
from lib.design import Design


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)
count = ExperimentVariable(
    name = "count",
    options = ["1", "2"]
)

units = Units(4)

des = (
    Design()
        .within_subjects(treatment)
        .between_subjects(count)
        .counterbalance(treatment)
        .limit_groups(4)
)

print(assign(units, des))