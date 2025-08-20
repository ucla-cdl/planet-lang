from planet import *


"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642772
"""

condition = ExperimentVariable(
    name = "condition",
    options = ["M1", "M2", "M3", "M4", "M5"]
)

subtask = ExperimentVariable(
    name = "subtask",
    options = ["S1", "S2", "S3", "S4", "S5"]
)

repeat = (
    Design()
    .num_trials(3)
)

task_des = (
    Design()
        .within_subjects(condition)
        .counterbalance(condition)
        .limit_plans(5)
)
condition_des = (
    Design()
        .within_subjects(subtask)
        .counterbalance(subtask)
        .limit_plans(5)
      
)
cross_des = cross(task_des, condition_des)
repeat_des = nest(inner=repeat, outer=cross_des)
units = Units(16)

assignment = assign(units, repeat_des)
print(assignment)