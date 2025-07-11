
import sys
sys.path.append("../")
from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.unit import Units
from lib.assignment import assign


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c", "d"]
)

units = Units(48)


des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
    
)

assignment = assign(units, des)

print(assignment)

