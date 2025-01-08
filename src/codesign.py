from z3 import *
from lib.orders import Sequence
from lib.assignment import Assignment

from lib.participant import Participants
from lib.variable import ExperimentVariable
import lib.candl as candl

# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
session = ExperimentVariable(
    name = "session",
    options = ["1", "2", "3"]
)


# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 

subjects = Participants(8)

# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(3) 

seq.force(0, variable = session, condition = "1")

seq.force(1, variable = session, condition = "2")

seq.force(2, variable = session, condition = "3")



# should the user have to create groups before passing to assignment?

# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment() # identify as within-subjects design
assignment.assign_to_sequence(subjects, seq, variables = [session])
final = assignment.eval()
print(final)