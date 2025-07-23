import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.nest import nest
from lib.unit import Units 
from lib.assignment import assign 

"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642611
"""

exercise_intensity = ExperimentVariable("Exercise Intensity", options=["low", "medium", "high"])
emotion_ve = ExperimentVariable("Emotion VE", options=["happiness", "sadness", "stress", "calmness"])

emotion_design = (
    Design()
    .within_subjects(emotion_ve)
    .counterbalance(emotion_ve)  
    .limit_groups(len(emotion_ve))
)

exercise_design = (
    Design()
    .within_subjects(exercise_intensity)
    .counterbalance(exercise_intensity)
    .limit_groups(len(exercise_intensity))
)

design = nest(inner = emotion_design, outer = exercise_design)
participants = Units(72)

assignment = assign(participants, design)
print(assignment)