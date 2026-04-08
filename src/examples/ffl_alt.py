from planet import * 
from planet.analysis import Analysis, compare

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
        .counterbalance(task)
        
)

interface_des = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
        .limit_plans(2)
)

number_des = (
    Design()
        .within_subjects(number)
        .counterbalance(number)
        .limit_plans(2)
      
)

cross_des = cross(interface_des, number_des)
des1 = nest(outer=task_des, inner=cross_des)

task_des = (
    Design()
        .within_subjects(task)
        .order(task, ["creation", "editing"])
        
)

cross_des = cross(interface_des, number_des)
des2 = nest(outer=task_des, inner=cross_des)

compare(des1, des2)

# des.to_latex()
# assignment = assign(units, des1)
# print(assignment)


      





