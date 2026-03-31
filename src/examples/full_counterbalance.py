from planet import *
import time
from planet.analysis import Analysis

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c"]
)

units = Units(48)


des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
        .num_trials(2)
)

assignment = assign(units, des)
print(assignment)
print(Analysis(des))

# assignment.to_latex()

