import sys
sys.path.append("../")

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.unit import Units 
from lib.assignment import assign 
from lib.nest import nest

"""
https://dl.acm.org/doi/pdf/10.1145/3544548.3581507

Not fully expressible.
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

des = (
    Design()
        .within_subjects(mode)
        .counterbalance(mode)
)

des2 = (
    Design()
        .within_subjects(task)
        .num_trials(2)
)

des = nest(inner=des2, outer=des)

assignment = assign(units, des)
print(assignment)

# NOTE: modify units table so we can assign multiple plans!
# des = (
#     Design()
#         .within_subjects(task)
# )

# print(assign(units, des))