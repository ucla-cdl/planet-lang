import sys
sys.path.append("../")

from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.nest import nest, cross
from lib.assignment import assign, assign_counterbalance
from lib.unit import Units


task = ExperimentVariable(
    name = "task",
    options = ["creation", "editing"]
)
units = Units(16)
des = (
    Design()
        .within_subjects(task)
        .absolute_rank(task, "creation", 1)
)

assignment = assign(units, des)
print(assignment)