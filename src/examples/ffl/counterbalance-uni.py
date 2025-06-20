import sys
sys.path.append("../")

from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design, nest, cross
from lib.assignment import assign, assign_counterbalance
from lib.unit import Units

interface = ExperimentVariable(
    name = "interface",
    options = ["ffl", "latex"]
)

units = Units(16)

des = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
)


assignment = assign(units, des)
print(assignment)
