import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))
from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 

"""
an experiment testing the effects of a VR interface combared to a
baseline using two tasks.
"""

interface = ExperimentVariable(
    name = "interface",
    options = ["VR", "baseline"]
)
task = ExperimentVariable(
    name = "task",
    options = ["painting", "basketball"]
)

units = Units(12)

interface_design = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
)
task_design = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)

design = nest(task_design, interface_design)
assign(units, design)
design.to_latex()













