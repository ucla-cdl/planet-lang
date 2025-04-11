import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))
from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 






"""
an experiment testing the effects of AR and VR interfaces combared to a
real-world scenario.
"""

interface = ExperimentVariable(
    name = "interface",
    options = ["AR", "VR", "Reality"]
)

units = Units(9)

design = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
        .limit_groups(len(interface))
)

assign(units, design)













interface = ExperimentVariable(
    name = "interface",
    options = ["AR", "VR", "Reality"]
)

task = ExperimentVariable(
    name = "task",
    options = ["basketball", "painting"]
)

units = Units(12)

interface_design = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
        .limit_groups(len(interface))
)
task_design = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
        .limit_groups(len(task))
)
design = nest(task_design, interface_design)

assign(units, design)






interface = ExperimentVariable(
    name = "interface",
    options = ["AR", "VR", "Reality"]
)

task = ExperimentVariable(
    name = "task",
    options = ["basketball", "painting"]
)

units = Units(12)

design = (
    Design()
        .within_subjects(multifact([interface, task]))
        .counterbalance(multifact([interface, task]))
        .limit_groups(len(multifact([interface, task])))
)

print(assign(units, design))


