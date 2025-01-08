from lib.orders import Sequence
from lib.assignment import Assignment, GroupAssignment
from lib.unit import Participants
from lib.variable import ExperimentVariable


# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
system = ExperimentVariable(
    name = "system",
    options = ["wall", "wall+ar"]
)
task = ExperimentVariable(
    name = "task",
    options = ["classification", "story"]
)

dataset = ExperimentVariable(
    name = "dataset",
    options = ["1", "2"]
)
# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
units = Participants(12)
# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(2) 

# DIFFERENT CONSTRAINT: first and second conditions in the 
# order never have the same assignment to the treatment variable
seq.different(0, 1, variable = system) 
seq.different(0, 1, variable = task) 
seq.different(0, 1, variable = dataset) 

# FORCE CONSTRAINT: assignmnet to the task variable for 
# the first and second conditions in the order is always creation
seq.force(0, task.get_condition("classification"))

seq.all_different()

# should the user have to create groups before passing to assignment?

# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment()
assignment.assign_to_sequence(units, seq, variables=[system, task, dataset])

final = assignment.eval()
print(final)

groups = assignment.get_groups()
participant_assignment = GroupAssignment(units, 1, groups)

members = participant_assignment.members


# this stalls when set to 4
# for example set this to 3 and num participants to 16
assignment = participant_assignment.eval()


print("\n participants mapping to groups")
print(assignment)

# NOTE: should be two ways to get within-subjects functionality 

