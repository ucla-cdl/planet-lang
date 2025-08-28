from planet import *

participants = Units(12)

task = ExperimentVariable(
    name = "task",
    options=["run", "walk", "sprint"]
)

interface = ExperimentVariable("interface", options=["baseline", "VR", "AR"])

task_design = (
    Design()
    .within_subjects(task)
    # .counterbalance(task, )
)

interface_design = (
    Design()
    .within_subjects(interface)
    # .counterbalance(interface)
)

# design = cross(interface_design, interface_design)
design = nest(inner=task_design, outer=interface_design)
print(assign(participants, design))

