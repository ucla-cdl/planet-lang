from z3 import *
from lib.participant import Participants
from lib.orders import Sequence
from lib.assignment import Assignment
from lib.variable import ExperimentVariable
from lib.blocks import BlockFactor


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



participants = Participants(2)
school = BlockFactor(levels = ["kirkwood", "ladue"])
age = BlockFactor(levels = ["young", "old"])
# groups = BlockFactor(levels=["a", "b", "c", "d"]) 

# conclusion: works with block factors... what do we want to store in each place?
# we should store constraint metadata in these classes and evaluate the constraint 
# in assignment, since they will build on each other 

sequence = Sequence(2) 

assignment = Assignment()

# participants.match(0,1, variable = task)
# sequence.match(0,1, variable = task)
# new Unit class
assignment.assign_to_blocks(blocks = [participants, sequence, school, age], variables = [treatment, task])

# NOTE: here we can actually construct constraints
# we knwo the dims of the unit

participants.all_different()
assignment.recieve_different_conditions(sequence)
# assignment.recieve_different_conditions(participants)

# # NOTE: should allow user to set this constraint accross all units
print(assignment.eval())

# groups.get_assignment()



