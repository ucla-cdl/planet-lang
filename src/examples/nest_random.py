import sys
sys.path.append("../")
from lib.variable import ExperimentVariable, multifact
from lib.unit import Units 
from lib.assignment import assign 
from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.nest import nest
from lib.replications import Replications

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

rep = Replications(2)


des1 = (
    Design()
        .within_subjects(treatment)
        # .counterbalance(treatment)
)

des2 = (
    Design()
        .within_subjects(task)
)

units = Units(10)




des = nest(inner=des1, outer=des2)
final = assign(units, des)
print(final)
