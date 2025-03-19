from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.assignment import assign
from lib.unit import Units


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c", "d", "e", "f"]
)


des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
)

units = Units(6)


assign(units, des)