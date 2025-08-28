from planet import *

# NOTE: need to make all different wrt. variables. Should this be under the hood though?
# ie. handle with cross instead of reasoning about counterbalanced vars independently 
treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["A", "B", "C", "D"]
)

test = ExperimentVariable(
    name = "test",
    options = ["x", "y"]
)

test2 = ExperimentVariable(
    name = "test2",
    options = ["X", "Y"]
)

units = Units(16)

des1 = (Design()
        .within_subjects(task)
        .counterbalance(task)
        .limit_plans(4)
)

des3 = (Design()
        .within_subjects(test)
        .counterbalance(test)
)

des4 = (Design()
        .within_subjects(test2)
        .counterbalance(test2)
)

d2 = nest(outer=des3, inner=des4)
d5 = cross(d2, des1)

print(assign(units, d5))