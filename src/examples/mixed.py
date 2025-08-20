from planet import *

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)
count = ExperimentVariable(
    name = "count",
    options = ["1", "2"]
)

units = Units(1)

des = (
    Design()
        .within_subjects(count)
        .between_subjects(treatment)
        # .counterbalance(count)
        # .limit_plans(4)
)

print(assign(units, des))