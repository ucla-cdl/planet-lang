import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 

gesture = ExperimentVariable("pronouns", options=[
    "watashi-kanji", "atashi", "ore", "boku", "watashi", "watakushi", "atakushi", "uchi", "jibun", "washi"] )

participants = Units(210)

design = (
    Design()
    .within_subjects(gesture)
)

assign(participants, design)

