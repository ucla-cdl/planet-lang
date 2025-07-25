from planet import *

"""
PLanet tutorial starter code
"""

interface = ExperimentVariable(
    name = "interface",
    options=["baseline", "VR", "AR"]
)

units = Units(12)

interface_design = (
    Design()
    .within_subjects(interface)
    .absolute_rank(interface, "baseline", 1)
)

assignment = assign(units, interface_design)
print(assignment)



task = ExperimentVariable(
    name = "task",
    options=["run", "walk", "sprint"]
)

task_design = (
    Design()
    .within_subjects(task)
    .counterbalance(task)
    .limit_groups(len(task))
)

# assignment = assign(units, task_design)
# print(assignment)


design = nest(inner=task_design, outer=interface_design)
assignment = assign(units, design)
print(assignment)


