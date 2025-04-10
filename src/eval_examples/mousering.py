import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest, cross
from lib.unit import Units 
from lib.assignment import assign 


"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642225
"""

input_method = ExperimentVariable("input", options=["touchpad", "airmouse", "mouseringdouble", "mouseringsingle"])

design = (
    Design()
    .within_subjects(input_method)
)

participants = Units(12)

assign(participants, design)