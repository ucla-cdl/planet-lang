from planet import *
from planet.analysis import Analysis

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)
count = ExperimentVariable(
    name = "count",
    options = ["1", "2"]
)

units = Units(1)

#FIXME. num trials are not correct
des = (
    Design()
        .within_subjects(count)
        .between_subjects(treatment) #problem with num trials and btw subjects
        .counterbalance(count)
        .limit_plans(4)
)



print(assign(units, des))
print(Analysis(des))