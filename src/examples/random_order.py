from planet import *
from planet.analysis import Analysis

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2"]
)


des = (
    Design()
        .within_subjects(treatment)
        .within_subjects(task)
        .counterbalance(task)
        .limit_plans(4) # NOTE: this does nothing for random plans :O
)

units = Units(8)


print(assign(units, des))
print(Analysis(des))