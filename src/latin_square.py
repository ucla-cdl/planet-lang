from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.unit import Units
from lib.assignment import assign

count = ExperimentVariable(
    name = "count",
    options = ["1", "2", "3", "4", "5"]
)

units = Units(25)

des = (
    Design()
        .within_subjects(count)
        .counterbalance(count)
        .limit_groups(len(count))
)



assign(units, des)