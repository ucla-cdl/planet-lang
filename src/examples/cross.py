from planet import *
from planet.analysis import Analysis, compare

# NOTE: need to make all different wrt. variables. Should this be under the hood though?
# ie. handle with cross instead of reasoning about counterbalanced vars independently 
treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["A", "B"]
)

num = ExperimentVariable(
    name = "num",   
    options = ["1", "2"]
)

units = Units(12)

des1 = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
     
)
# # note: set / argv because no order
des2 = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)

des3 = (
    Design()
        .within_subjects(num)
        .counterbalance(num)
)

des4 = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
        .within_subjects(treatment)
        .counterbalance(treatment)
        .limit_plans(2)

)
des = cross(des2, des1)
# des = nest(inner=des, outer=des3)

print(assign(units, des))
print(Analysis(des))
compare(des, des4)  