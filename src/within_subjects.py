from z3 import *
from lib.orders import Sequence
from lib.assignment import Assignment
from lib.unit import Unit
from lib.unit import Participants
from lib.variable import ExperimentVariable
import lib.candl as candl
from lib.blocks import BlockFactor

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
# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 
#NOTE: something is weird with this for creating groups
subjects = Participants(12)
# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(1) 


seq.all_different()

chronotype_attr = BlockFactor(levels = ["morning", "night"])
subjects.add_attribute(chronotype_attr)
# should the user have to create groups before passing to assignment?

# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment() # identify as within-subjects design
assignment.assign_to_sequence(subjects, seq, variables = [chron, daytime])

print(assignment.eval())
groups = assignment.get_groups().expand_groups(int(8))

time = BlockFactor(levels = ["morning", "night"])
chron = BlockFactor(levels = ["morning", "night"])
# chron.force(1, variable=chronotype_attr, condition = "morning")
chron.force(1, variable=chronotype_attr, condition = "night")


assignment.assign_participants_to_groups(subjects, 2, groups, never_occur_together=True, blocks = [time, chron])