from planet import *

count = ExperimentVariable(
    name = "count",
    options = ["1", "2", "3"]
)

alpha = ExperimentVariable(
    name = "alpha",
    options = ["a", "b", "c", "d"]
)

units = Units(4)

multi = multifact(
    [count,
    alpha]
)

des = (
    Design()
        # .within_subjects(count)
        .within_subjects(alpha)
        .num_trials(3)
        # .counterbalance(count)
        .counterbalance(alpha)
)


print(assign(units, des))






