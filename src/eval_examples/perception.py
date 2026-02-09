from planet import *

'''
https://dl.acm.org/doi/pdf/10.1145/3544548.3581485
'''

augmentation_type = ExperimentVariable("Type of Augmentation", options=["Sensory", "Motor", "Cognitive"])
condition = ExperimentVariable("Condition", options=["Disability", "No Disability"])
participants = Units(506)

design = (
    Design()
    .between_subjects(augmentation_type)
    .between_subjects(condition)
)

print(assign(participants, design))
