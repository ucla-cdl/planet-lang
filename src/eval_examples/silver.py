import sys
sys.path.append("../")

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.unit import Units 
from lib.assignment import assign 

gesture = ExperimentVariable("pronouns", options=[
    "watashikanji", "atashi", "ore", "boku", "watashi", "watakushi", "atakushi", "uchi", "jibun", "washi"] )

participants = Units(210)

design = (
    Design()
    .within_subjects(gesture)
)

print(assign(participants, design))

