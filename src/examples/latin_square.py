from planet import *


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
        .limit_plans(len(multifact([interface, task])))
        .num_trials(6)
)

print(assign(units, design))


