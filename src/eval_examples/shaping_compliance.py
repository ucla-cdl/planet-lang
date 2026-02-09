from planet import *
"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3641907
"""

number_of_grains = ExperimentVariable("Number of Grains", options=["9", "19", "39"])
electrode_conditions = ExperimentVariable("Electrode Conditions", options=["0", "4", "6", "9"])

participants = Units(12) 
repititions = (
    Design()
    .num_trials(3)
)

multi = multifact([number_of_grains, electrode_conditions])

design = (
    Design()
    .within_subjects(multi)
    .counterbalance(multi)
    .limit_plans(len(number_of_grains) * len(electrode_conditions))
)
 
final = nest(outer=repititions, inner=design)
print(assign(participants, final))