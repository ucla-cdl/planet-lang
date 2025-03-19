from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c", "d"]
)


des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
    
)



print(des)