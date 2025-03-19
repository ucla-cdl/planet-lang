from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design


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


des = (
    Design()
        .within_subjects(task, number)
        .between_subjects(interface)
        .counterbalance(task)
        .counterbalance(number)
        .num_trials(2)
)

print(des)
