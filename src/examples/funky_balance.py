from planet import *
from planet.analysis import Analysis


count = ExperimentVariable(
    name = "count",
    options = ["1", "2"]
)

alpha = ExperimentVariable(
    name = "alpha",
    options = ["a", "b", "c", "d"]
)


units = Units(24)

multi = multifact(
    [count,
    alpha]
)

# NOTE: counterbalancing first will break. Add a warning :) 
des = (
    Design()
        # .within_subjects(count)
        .within_subjects(alpha)
        .num_trials(2)
        # .counterbalance(count)
        .counterbalance(alpha)
        # .limit_plans(4)
)


print(assign(units, des))
print(Analysis(des))
