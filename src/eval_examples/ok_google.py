import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 

"""
https://dl.acm.org/doi/pdf/10.1145/3544548.3581507

Not fully expressible.
"""

mode = ExperimentVariable(
    name = "mode",
    options = ["M", "SB", "CD"]
)

units = Units(51)

des = (
    Design()
        .between_subjects(mode)
)

assignment = assign(units, des)