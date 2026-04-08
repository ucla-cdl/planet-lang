from planet import * 
from planet.analysis import Analysis

task = ExperimentVariable(
    name = "task",
    options = ["creation", "editing"]
)

number = ExperimentVariable(
    name = "number",
    options = ["1", "2"]
)

interface = ExperimentVariable(
    name = "interface",
    options = ["ffl", "latex"]
)


units = Units(16)

task_des = (
    Design()
        .within_subjects(task)
        .order(task, ["creation", "editing"])
)

interface_des = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
)

number_des = (
    Design()
        .within_subjects(number)
        .counterbalance(number)  
)

cross_des = cross(interface_des, task_des)
des = nest(outer=number_des, inner=cross_des)

# des.to_latex()
assignment = assign(units, des)
print(assignment)
print(Analysis(des))