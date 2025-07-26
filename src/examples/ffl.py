from planet import * 

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
        .start_with(task, "creation")
        
)

interface_des = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
        .limit_groups(2)
)

number_des = (
    Design()
        .within_subjects(number)
        .counterbalance(number)
        .limit_groups(2)
      
)

cross_des = cross(interface_des, number_des)
des = nest(outer=task_des, inner=cross_des)

des.to_latex()
assignment = assign(units, des)
print(assignment)











