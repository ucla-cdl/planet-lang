import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.unit import Units 
from lib.assignment import assign 

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