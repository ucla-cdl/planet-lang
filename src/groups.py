from lib.orders import Sequence
from lib.assignment import Assignment
from lib.participant import Participants
from lib.variable import ExperimentVariable
# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
participants = ExperimentVariable(
    name = "participants",
    options = ["p1", "p2", "p3", "p4", "p5", "p6"]
)
chronotype = ExperimentVariable(
    name = "chronotype",
    options = ["morning", "night"]
)


# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 

groups = Participants(2)
# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
grouping = Sequence(3) 
# seq.match(0, 1, treatment)
# seq.force(0, treatment, "A")


groups.all_different()
grouping.all_different()
# should the user have to create groups before passing to assignment?

# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment() # identify as within-subjects design

assignment.all_different()
assignment.force

assignment.assign_to_sequence(groups, grouping, variables = [participants])
final = assignment.eval()

print(final)