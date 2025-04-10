import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
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
)

assign(participants, design)