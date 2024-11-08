from z3 import *
from lib.participant import Participants
from lib.orders import Sequence
from lib.assignment import Assignment
from lib.variable import ExperimentVariable
from test.block_factor import BlockFactor


# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
treatment = ExperimentVariable(
    name = "treatment",
    options = ["A", "B", "C", "D"]
)

participants = Participants(4)

# conclusion: works with block factors... what do we want to store in each place?
# we should store constraint metadata in these classes and evaluate the constraint 
# in assignment, since they will build on each other 
# sequence = BlockFactor(levels=["a", "b", "c", "d"]) 
sequence = Sequence(4, treatment) 

assignment = Assignment()

# new Unit class
assignment.assign_to_sequence(participants, sequence)

# NOTE: here we can actually construct constraints
# we knwo the dims of the unit

# # new Condiitons class
assignment.compose_conditions(treatment)

sequence.different(0, 1, treatment)

assignment.recieve_different_conditions(participants) # by default?
assignment.recieve_different_conditions(sequence) 

# # NOTE: should allow user to set this constraint accross all units


print(assignment.generate())



