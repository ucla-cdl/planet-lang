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

multi = multifact([interface, task])

design = (
    Design()
        .within_subjects(multi)
        .counterbalance(multi)
        .limit_plans(len(multi))
        .num_trials(6)
)

print(assign(units, design))


