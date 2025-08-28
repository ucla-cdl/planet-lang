from planet import *

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