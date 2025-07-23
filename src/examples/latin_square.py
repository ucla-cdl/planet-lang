import sys
sys.path.append("../")
from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.nest import nest
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

task = ExperimentVariable(
    name = "task",
    options = ["basketball", "painting"]
)

units = Units(8)

design = (
    Design()
        .within_subjects(multifact([interface, task]))
        .counterbalance(multifact([interface, task]))
        .limit_groups(len(multifact([interface, task])))
)

print(assign(units, design))


