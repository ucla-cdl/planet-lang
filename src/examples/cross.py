from planet import *


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

units = Units(12)

des1 = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
        # .start_with(treatment, "a", 1)
     
)
# # note: set / argv because no order
des2 = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
     
)

print(assign(units, cross(des1, des2)))