from planet import *

"""
PLanet tutorial starter code
"""


intervention = ExperimentVariable(
    name = "intervention",
    options=["baseline", "custom"]
)

task = ExperimentVariable(
    name = "task",
    options=["1", "2"]
)

participants = Units(10)

design = (
    Design()
    .between_subjects(intervention)
)

block = (
    Design()
    .num_trials(2)
)


design = nest(inner=block, outer=design)
design = nest(outer = design,
              inner = Design()
               .within_subjects(task)
               .counterbalance(task)
)

assignment = assign(participants, design)
print(assignment)