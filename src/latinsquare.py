from z3 import *
from test.participants import Participants
from test.sequence import Sequence
from test.assignment import Assignment
from lib.variable import ExperimentVariable


# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
treatment = ExperimentVariable(
    name = "treatment",
    options = ["A", "B", "C", "D"]
)

participants = Participants(4)
sequence = Sequence(4) 

assignment = Assignment()

# new Unit class
assignment.compose_units(participants, sequence)
# NOTE: here we can actually construct constraints
# we knwo the dims of the unit

# new Condiitons class
assignment.compose_conditions(treatment)

# function name not capturing program
assignment.recieve_different_conditions(participants) # by default?
assignment.recieve_different_conditions(sequence) 

# NOTE: should allow user to set this constraint accross all units


print(assignment.generate())



