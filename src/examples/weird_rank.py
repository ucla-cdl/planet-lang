from planet import *


task = ExperimentVariable(
    name = "task",
    options = ["a", "b", "c", "d"]
)


# this is a possible bug. Come back to this! 
units = Units(16)
des = (
    Design()
        .within_subjects(task)
        .absolute_rank(task, "b", 1)
        # .num_trials(2)
        .limit_plans(3)
)

assignment = assign(units, des)
print(assignment)