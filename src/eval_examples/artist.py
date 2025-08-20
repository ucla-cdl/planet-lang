from planet import *


"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642772
"""

task = ExperimentVariable(
    name = "task",
    options = ["coffee", "room"]
)

condition = ExperimentVariable(
    name = "condition",
    options = ["ARTiST", "baseline"]
)

task_des = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)
condition_des = (
    Design()
        .within_subjects(condition)
        .counterbalance(condition)
      
)
cross_des = cross(task_des, condition_des)
units = Units(16)

assignment = assign(units, cross_des)
print(assignment)