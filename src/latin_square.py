from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.unit import Units
from lib.assignment import assign

count = ExperimentVariable(
    name = "count",
    options = ["1", "2", "3"]
)

units = Units(27)



des = (
    Design()
        .within_subjects(count)
        .counterbalance(count)
        .limit_groups(len(count))
)



assign(units, des)
print(des)