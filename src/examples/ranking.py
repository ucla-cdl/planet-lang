from planet import *


task = ExperimentVariable(
    name = "task",
    options = ["a", "b", "c"]
)
units = Units(16)
des = (
    Design()
        .within_subjects(task)
        .absolute_rank(task, "b", 1)
)

assignment = assign(units, des)
print(assignment)