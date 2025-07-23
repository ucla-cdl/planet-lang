import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.nest import nest
from lib.unit import Units 
from lib.assignment import assign 
from lib.replications import Replications


"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3642225
"""

input_method = ExperimentVariable("input", options=["touchpad1", "touchpad2", "airmouse1", "airmouse2", "mouseringdouble1", "mouseringdouble2", "mouseringdouble3", "mouseringdouble4", "mouseringsingle1", "mouseringsingle2", "mouseringsingle3", "mouseringsingle4"])
repitition = Replications(2)


design = (
    Design()
    .within_subjects(input_method)
    .counterbalance(input_method)
    .limit_groups(12)
)

design = nest(inner=repitition, outer=design)
participants = Units(12)

print(assign(participants, design))