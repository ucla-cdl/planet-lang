import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 

"""
https://dl.acm.org/doi/pdf/10.1145/3544548.3580672
"""

intervention = ExperimentVariable("Intervention", options=["Control", "Causal AI Explanation", "AI-Framed Questioning"])
statement_validity = ExperimentVariable("Statement Validity", options=["Valid", "Invalid"])

participants = Units(204)

design = (
    Design()
    .between_subjects(intervention)
    .within_subjects(statement_validity)
)

assign(participants, design)
