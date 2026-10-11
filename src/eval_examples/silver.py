from planet import *

"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642303
"""
gesture = ExperimentVariable("pronouns", options=[
    "watashikanji", "atashi", "ore", "boku", "watashi", "watakushi", "atakushi", "uchi", "jibun", "washi"] )

participants = Units(210)

design = (
    Design()
    .within_subjects(gesture)
)

print(assign(participants, design))

