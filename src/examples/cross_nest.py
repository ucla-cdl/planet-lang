from planet import *
from planet.analysis import Analysis

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
    options = ["x", "y", "z"]
)

test2 = ExperimentVariable(
    name = "test2",
    options = ["X", "Y", "Z"]
)

multi = multifact([test, test2])

units = Units(16)

des1 = (Design()
        .within_subjects(task)
        .counterbalance(task)
        .limit_plans(4)
)

des2 = (Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
)

# EDGE CASE!
des3 = (Design()
        .within_subjects(test)
        .counterbalance(test)
        .within_subjects(test2)
        .counterbalance(test2)
        .limit_plans(3)
)

# des4 = (Design()
#         .within_subjects(test2)
#         .counterbalance(test2)
# )

# d2 = nest(outer=des3, inner=des4)
# d5 = cross(d2, des1)

# d2 = nest(inner=des3, outer=des4)
d5 = nest(inner=des3 , outer=des2)

print(assign(units, d5))
print(Analysis(d5))