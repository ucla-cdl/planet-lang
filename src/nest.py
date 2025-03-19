from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.design import nest


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
        .limit_groups(2)
)


print(des1)
print(des2)

des = nest(des2, des1)

test = nest(des3, des)

print(des)
print(test)