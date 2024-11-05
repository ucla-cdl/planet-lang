from z3 import *
from lib.orders import PossibleOrders
from lib.assignment import Assignment
from lib.unit import Unit
from lib.variable import ExperimentVariable
import itertools

def construct_conditions(*argv):
    return list(itertools.product(*list(arg.conditions for arg in argv)))

# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
daytime = ExperimentVariable(
    name = "daytime",
    options = ["morning", "night"]
)
comp = ExperimentVariable(
    name = "composition",
    options = ["homo", "hetero"]
)
chron = ExperimentVariable(
    name = "chronotype",
    options = ["morning", "night"]
)

units = [Unit(i) for i in range(20)] 
conditions = construct_conditions(daytime, comp, chron)

# need constraint that 4 are morning 5 are night, and that we see all conditions


# assignment = Assignment(units = units, groups = possible_orders)

