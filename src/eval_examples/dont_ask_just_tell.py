from planet import *

"""
https://dl.acm.org/doi/pdf/10.1145/3544548.3580672
"""

# NOTE to self: ensure no hyphens in condition strings
intervention = ExperimentVariable("Intervention", options=["Control", "Causal AI Explanation", "AIFramed Questioning"])
statement = ExperimentVariable("Statement", options=[f"{i+1}" for i in range(40)])

participants = Units(204)

design = (
    Design()
    .between_subjects(intervention)
    .within_subjects(statement)
    .num_trials(10)
)

print(assign(participants, design))
