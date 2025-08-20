from planet import *

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2"]
)

day = ExperimentVariable(
    name = "day",
    options = ["morning", "night", "afternoon", "evening"]
)

test = multifact([treatment, task])

des = (
    Design()
        .within_subjects(test)
        .counterbalance(test)
)

units = Units(1)

print(assign(units, des))