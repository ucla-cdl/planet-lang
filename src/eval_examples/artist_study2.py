import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.nest import cross, nest
from lib.unit import Units 
from lib.assignment import assign 
from lib.replications import Replications


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

repeat = Replications(3)

task_des = (
    Design()
        .within_subjects(condition)
        .counterbalance(condition)
        .limit_groups(5)
)
condition_des = (
    Design()
        .within_subjects(subtask)
        .counterbalance(subtask)
        .limit_groups(5)
      
)
cross_des = cross(task_des, condition_des)
repeat_des = nest(inner=repeat, outer=cross_des)
units = Units(16)

assignment = assign(units, repeat_des)
print(assignment)