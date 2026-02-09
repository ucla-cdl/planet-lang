from planet import *


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2"]
)


combine = multifact([treatment, task])

# NOTE: limit plans does not limit randomization
des = (
    Design()
        .within_subjects(treatment)
        .within_subjects(task)
        .counterbalance(combine)
        .limit_plans(4)
)

units = Units(12)

print(assign(units, des))