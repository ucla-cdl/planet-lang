from planet import *

task = ExperimentVariable(
    name = "task",
    options = ["c", "e"]
)

number = ExperimentVariable(
    name = "number",
    options = ["1", "2", "3", "4"]
)

units = Units(16)

block = (
    Design()
    .num_trials(2)
)

task_des = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)


number_des = (
    Design()
        .within_subjects(number)
        .limit_groups(4)
      
)



task_des = nest(inner=block, outer=task_des)

print(assign(units, task_des))

cross_des = cross(task_des, number_des)

assignment = assign(units, cross_des)
print(assignment)






