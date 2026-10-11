from planet import *

gesture = ExperimentVariable("Gesture", options=[
    "Tap", "Double Tap", "Swipe Left", "Swipe Right",  "Swipe Up", "Swipe Down", 
    "Clockwise Swipe", "Counterclockwise Swipe", "Pinch", "Spread", "Rest"
])

participants = Units(10)

# Ten trials of all eleven gestures in a randomized order (110 recordings per
# participant): ten repetition blocks, each a random order of the eleven gestures.
design = (
    Design()
    .within_subjects(gesture)
)

repetitions = (
    Design()
    .num_trials(10)
)

final = nest(inner=design, outer=repetitions)
print(assign(participants, final))