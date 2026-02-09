from planet import *


"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642225
"""

input_method = ExperimentVariable("input", options=["touchpad1", "touchpad2", "airmouse1", "airmouse2", "mouseringdouble1", "mouseringdouble2", "mouseringdouble3", "mouseringdouble4", "mouseringsingle1", "mouseringsingle2", "mouseringsingle3", "mouseringsingle4"])
page = ExperimentVariable("page", options = [f"{i+1}" for i in range(10)])
repitition = (
    Design()
    .num_trials(5)
)


design = (
    Design()
    .within_subjects(input_method)
    .counterbalance(input_method)
    .limit_plans(12)
)

page_design = (
    Design()
    .within_subjects(page)
)

design = nest(inner=page_design, outer=design)
design = nest(inner = repitition, outer = design)
participants = Units(12)
print(assign(participants, design))