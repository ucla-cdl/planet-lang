import sys
sys.path.append("../")
from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.unit import Units
from lib.assignment import assign



count = ExperimentVariable(
    name = "count",
    options = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]
)

units = Units(20)

des = (
    Design()
        .within_subjects(count)
        .counterbalance(count)
        .limit_plans(len(count) * 2)
)


print(assign(units, des))






