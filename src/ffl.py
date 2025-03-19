from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design, nest
from lib.assignment import assign, assign_counterbalance
from lib.unit import Units



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

print(task_des)

interface_des = (
    Design()
        .within_subjects(interface, number)
        .counterbalance(interface)
        .counterbalance(number)
        .num_trials(2)
        .limit_groups(4)
)

des = nest(interface_des, task_des)
print(des)


assign_counterbalance(units, des)

print(task_des)

# print(task_des)
# print(interface_des)

# print(des)