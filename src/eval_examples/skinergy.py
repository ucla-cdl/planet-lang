import sys
sys.path.append("../")

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.unit import Units 
from lib.assignment import assign 

gesture = ExperimentVariable("Gesture", options=[
    "Tap", "Double Tap", "Swipe Left", "Swipe Right",  "Swipe Up", "Swipe Down", 
    "Clockwise Swipe", "Counterclockwise Swipe", "Pinch", "Spread", "Rest"
])

participants = Units(10)

design = (
    Design()
    .within_subjects(gesture)
    .num_trials(10)
)

print(assign(participants, design))