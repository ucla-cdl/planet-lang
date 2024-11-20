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
    options = ["A", "B"]
)
task = ExperimentVariable(
    name = "task",
    options = ["A", "B"]
)

# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 

subjects = Participants(4)
# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(4) 
# seq.different(0, 1, treatment)
seq.match(2, 3, treatment)
# subjects.match(0,1, task)
seq.force(0, task, "A")
seq.different(0, 1, task)
# seq.force(2, treatment, "A")
seq.force(0, treatment, "A")

# for i in range(0, seq.n-2, 1):
#     seq.different(i, i+1, variable = treatment)
#     seq.different(i, i+2, variable = treatment)

# seq.different(all((i, i+1, i+2)), variable = treatment)

seq.all_different()
# should the user have to create groups before passing to assignment?
# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment() # identify as within-subjects design
assignment.assign_to_sequence(subjects, seq, variables = [treatment, task])
final = assignment.test()

print(assignment.eval())
