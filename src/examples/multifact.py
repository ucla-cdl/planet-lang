from planet import *


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2"]
)


# des = (
#     Design()
#         .within_subjects(multifact([treatment, task]))
#         .counterbalance(multifact([treatment, task]))
# )

units = Units(12)

# print(assign(units, des))

# fix width problems
task_design = (
    Design()
    .within_subjects(task)
    .within_subjects(treatment)
    .counterbalance(task)
    .counterbalance(treatment)
    .num_trials(2)
)
print(assign(units, task_design))