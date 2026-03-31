from planet import *
from planet.analysis import Analysis

"""
PLanet tutorial starter code
"""


intervention = ExperimentVariable(
    name = "intervention",
    options=["1", "2","3"]
)

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c"]
)

participants = Units(10)

design = (
    Design()
    .within_subjects(intervention)
    .counterbalance(intervention)
    .limit_plans(3)
    # .between_subjects(treatment)
    # .counterbalance(treatment)
)


# treatment_design = (
#     Design()
#     .within_subjects(treatment)
#     .counterbalance(treatment)
# )

# rep = (
#     Design()
#     .num_trials(2)
# )

# design = nest(inner=rep, outer=design)
# design=cross(design, treatment_design)

assignment = assign(participants, design)
print(assignment)
print(Analysis(design))