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
    .counterbalance(task, )
    .limit_plans(3)
    
)

interface_design = (
    Design()
    .within_subjects(interface)
    .counterbalance(interface, )
    .num_trials(2)
)

# design = cross(interface_design, interface_design)
design = nest(inner=interface_design, outer=task_design)
print(assign(participants, interface_design))




# block = (
#     Design()
#     .num_trials(2)
# )

# task_design = (
#     Design()
#     .within_subjects(task)
#     .counterbalance(task, )
#     .limit_plans(len(task))
# )

# # NOTE: task_design is the latin sqaure we defined in Step 3. 
# design = nest(inner=block, outer=task_design)
# print(assign(participants, design))
