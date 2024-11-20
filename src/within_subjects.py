from z3 import *
from lib.orders import Sequence
from lib.assignment import Assignment
from lib.unit import Unit
from lib.participant import Participants
from lib.variable import ExperimentVariable
import lib.candl as candl

# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
treatment = ExperimentVariable(
    name = "treatment",
    options = ["A", "B", "C"]
)

# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 

subjects = Participants(3)
# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(3) 
# seq.match(0, 1, treatment)
# seq.force(0, treatment, "A")


# THIS WORKS, YAYYYY!!!
# subjects.different(0, 1, variable = treatment)
# subjects.different(2,3, variable=treatment)

seq.all_different()
subjects.all_different()

# should the user have to create groups before passing to assignment?

# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment() # identify as within-subjects design
assignment.assign_to_sequence(subjects, seq, variables = [treatment])
# final = assignment.eval()
# print(final)
assignment.test()
assignment.assign_participants_to_groups()