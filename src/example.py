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
        .within_subjects(task)
        .between_subjects(interface, number)
        .counterbalance(task)
        .start_with(task, "creation")
        # .num_trials(2)
)

print(des)
