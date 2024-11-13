from z3 import *
from lib.assignment import Assignment
from lib.unit import Unit
from lib.orders import Sequence
from lib.variable import ExperimentVariable
import itertools
from lib.participant import Participants

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
    options = ["homogeneous", "heterogeneous"]
)
chron = ExperimentVariable(
    name = "chronotype",
    options = ["morning", "night"]
)

question = ExperimentVariable(
    name = "question",
    options = ["insight", "inc"]
)

seq = Sequence(2, daytime, comp, chron, question)
seq.match(0, 1, variable = daytime)
seq.match(0, 1, comp)
seq.match(0, 1, chron)
seq.different(0, 1, question)

subjects = Participants(16)

assignment = Assignment() # identify as within-subjects design
assignment.assign_to_sequence(subjects, seq, variables = [daytime, comp, chron, question])
final = assignment.eval()


for group in final:
    print(group)












# need constraint that 4 are morning 5 are night, and that we see all conditions


# assignment = Assignment(units = units, groups = possible_orders)

