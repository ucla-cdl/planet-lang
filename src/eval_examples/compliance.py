import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.unit import Units 
from lib.assignment import assign 
from lib.replications import Replications
from lib.nest import nest



"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3641907
"""

number_of_grains = ExperimentVariable("Number of Grains", options=["9", "19", "39"])
electrode_conditions = ExperimentVariable("Electrode Conditions", options=["0", "4", "6", "9"])

participants = Units(12) 
repititions = Replications(3)

design = (
    Design()
    .within_subjects(multifact([number_of_grains, electrode_conditions]))
    .counterbalance(multifact([number_of_grains, electrode_conditions]))
    .limit_groups(len(number_of_grains) * len(electrode_conditions))
)
 
final = nest(outer=repititions, inner=design)
print(assign(participants, final))