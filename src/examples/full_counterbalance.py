from planet import *
import time

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c"]
)

units = Units(48)


des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
)

assignment = assign(units, des)


assignment.to_latex()

