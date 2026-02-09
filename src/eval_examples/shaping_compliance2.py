from planet import *

"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3641907
"""

shape = ExperimentVariable("shape", options=["large", "small",
                                              "horizontal", "vertical", "triangle"])

participants = Units(12) 
repititions = (
    Design()
    .num_trials(3)
)

design = (
    Design()
    .within_subjects(shape)
)
 
final = nest(outer=repititions, inner=design)
print(assign(participants, final))