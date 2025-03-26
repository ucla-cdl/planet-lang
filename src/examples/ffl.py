from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design, nest, cross
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

cross_des = cross(interface_des, number_des)
des = nest(cross_des, task_des)

des.to_latex()
assignment = assign(units, des)
print(assignment)









