
import sys
sys.path.append("../")
from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.nest import nest
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

design = nest(outer=interface_design, inner=task_design)
print(assign(units, design))














