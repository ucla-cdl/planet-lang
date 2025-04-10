import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 

"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642217
"""

interface = ExperimentVariable(
    name = "interface",
    options = ["rambler", "baseline"]
)


units = Units(12)

des = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
)

des.to_latex()
assignment = assign(units, des)
print(assignment)