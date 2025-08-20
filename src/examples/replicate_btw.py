from planet import *

"""
PLanet tutorial starter code
"""


intervention = ExperimentVariable(
    name = "intervention",
    options=["baseline", "custom"]
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

design = nest(inner=design, outer=block)
assignment = assign(participants, design)
print(assignment)