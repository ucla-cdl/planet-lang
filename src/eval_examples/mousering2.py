from planet import *

"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642225
"""

input_method = ExperimentVariable("input", options=["touchpad", "airmouse", "mouseringdouble", "mouseringsingle"])
round = (
    Design()
    .num_trials(5)
)
repeat = (
    Design()
    .num_trials(10)
)


design = (
    Design()
    .within_subjects(input_method)
    .counterbalance(input_method)
    .limit_plans(12)
)


design = nest(inner=repeat, outer=design)
design = nest(inner = design, outer = round)
participants = Units(12)

print(assign(participants, design))