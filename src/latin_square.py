from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design


count = ExperimentVariable(
    name = "count",
    options = ["1", "2", "3", "4", "5"]
)


des = (
    Design()
        .within_subjects(count)
        .counterbalance(count)
        .limit_groups(len(count))
)

print(des)
