from planet import *

gesture = ExperimentVariable("pronouns", options=[
    "watashikanji", "atashi", "ore", "boku", "watashi", "watakushi", "atakushi", "uchi", "jibun", "washi"] )

participants = Units(210)

design = (
    Design()
    .within_subjects(gesture)
)

print(assign(participants, design))

