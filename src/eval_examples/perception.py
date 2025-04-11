import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 

augmentation_type = ExperimentVariable("Type of Augmentation", options=["Sensory", "Motor", "Cognitive"])
condition = ExperimentVariable("Condition", options=["Disability", "No Disability"])
participants = Units(506)

design = (
    Design()
    .between_subjects(augmentation_type)
    .between_subjects(condition)
)

assign(participants, design)
