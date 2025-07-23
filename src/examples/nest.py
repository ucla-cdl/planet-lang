import sys
sys.path.append("../")
from lib.variable import ExperimentVariable, multifact
from lib.unit import Units 
from lib.assignment import assign 
from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.nest import nest


# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
treatment = ExperimentVariable( 
    name = "treatment",
    options = ["A", "B"]
)
task = ExperimentVariable(
    name = "task",
    options = ["a", "b"]
)

test = ExperimentVariable(
    name = "test",
    options = ["x", "y"]
)

test2 = ExperimentVariable(
    name = "test2",
    options = ["X", "Y"]
)

des1 = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
        # .limit_groups(2)
)

des2 = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
        # .limit_groups(2)
)

des3 = (Design()
        .within_subjects(test)
        .counterbalance(test)

)

des4 = (Design()
        .within_subjects(test2)
        .counterbalance(test2)
        .limit_groups(2)
)

units = Units(48)

des = nest(inner=des2, outer=des1)


mega = nest(inner=des3, outer=des)
# mega.to_latex()
print(assign(units, mega))