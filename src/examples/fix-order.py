from planet import *
from planet.analysis import Analysis


task = ExperimentVariable(
    name = "task",
    options = ["a", "b", "c", "d"]
)

# this is a possible bug. Come back to this! 
units = Units(16)
des = (
    Design()
        .within_subjects(task)
        .order(task, ["a", "d", "c", "b"])
)

assignment = assign(units, des)
print(assignment)

print(Analysis(des))