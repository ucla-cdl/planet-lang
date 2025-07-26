from planet import *
"""
https://dl.acm.org/doi/pdf/10.1145/3544548.3581507
"""

mode = ExperimentVariable(
    name = "mode",
    options = ["M", "SB", "CD"]
)

task = ExperimentVariable(
    name = "task",
    options = [f"{i+1}" for i in range(6)]
)

units = Units(51)


block = (
    Design()
    .num_trials(2)
)

mode_des = (
    Design()
        .within_subjects(mode)
        .counterbalance(mode)
        .limit_groups(3)
)
mode_des = nest(inner=block, outer=mode_des)

task_des = (
    Design()
        .within_subjects(task)
)

des = cross(mode_des, task_des)
assignment = assign(units, des)
print(assignment)