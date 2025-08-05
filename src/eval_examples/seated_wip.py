from planet import *

"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642395
"""

footstep = ExperimentVariable(
    name = "footstep",
    options = ["fore", "rear", "full"]
)

posture = ExperimentVariable(
    name = "posture",
    options = ["straight", "back", "desk"]
)

units = Units(18)
multi = multifact([footstep, posture])

des = (
    Design()
        .within_subjects(multi)
        .counterbalance(multi)
        .limit_groups(len(multi))
)

assignment = assign(units, des)
print(assignment)