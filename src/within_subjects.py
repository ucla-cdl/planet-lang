from z3 import *
from lib.orders import Sequence
from lib.assignment import Assignment, GroupAssignment
from lib.unit import Unit
from lib.unit import Participants
from lib.variable import ExperimentVariable
import lib.candl as candl
from lib.blocks import BlockFactor
import time as foo

# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
chron = ExperimentVariable(
    name = "chronotype",
    options = ["morning", "night"]
)
daytime = ExperimentVariable(
    name = "daytime",
    options = ["morning", "night"]
)
comp = ExperimentVariable(
    name = "composition",
    options = ["heterogeneous", "homogeneous"]
)
# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 
#NOTE: something is weird with this for creating groups
subjects = Participants(24)
# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(1) 


# seq.all_different()
# subjects.all_different()
# connect this to blocks, how they are related 
# represent same datatype
chronotype_attr = BlockFactor(levels = ["morning", "night"])
subjects.add_attribute(chronotype_attr)
# should the user have to create groups before passing to assignment?

# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment() # identify as within-subjects design
# overloaded operator, pass ubjects here ? 

assignment.assign_to_sequence(subjects, seq, variables = [daytime, chron, comp])

print(assignment.eval())

groups = assignment.get_groups().expand_groups(int(16))

# members = groups.get_members()

attrs = groups.get_attributes()
time = attrs[0]
chron = attrs[1]
comp = attrs[2]

# should I apply the constraints to subject? or the block variable?
# for subject assignment, I think we can infer that we place constraints 
# on the participant? Some of these are constraints on the actual variable,
# while others are on the specific groups and their members. Rethink this. 
subjects.all_match(chronotype_attr, wrt = comp, level = 0) # group_members.all_match(wrt: dim)
# add same optional dim param to all_different. 

subjects.all_different() # this is actually group_members.all_different()
subjects.majority(0, 0, chron, chronotype_attr) # group_members.majority()
subjects.majority(1, 1, chron, chronotype_attr) # group_members.majority()



subjects.distinguish(time) #  variable-type constraint... all_different?
subjects.never_occur_together() # this is a variable constraint, so we can leave this
# THis constraint is expensive



participant_assignment = GroupAssignment(subjects, 2, groups)
t = foo.time()
# this stalls when set to 4
# for example set this to 3 and num participants to 16
assignment = participant_assignment.eval()
print(foo.time() - t)


print("\n participants mapping to groups")
print(assignment)
