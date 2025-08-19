from planet import *


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2", "3"]
)

test = multifact([treatment, task])

des = (
    Design()
        .within_subjects(test)
        # .counterbalance(test)
        # .limit_plans(9)
)

units = Units(1)

print(assign(units, des))