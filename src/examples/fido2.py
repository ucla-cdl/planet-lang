""" The design: 

We used a between-groups design to identify the diferences be-
tween platform and roaming authentication on smartphones.

We randomly distributed the participants into two groups: The study
group used platform authentication with Touch ID (Group P), while
the control group used roaming authentication with a YubiKey

FIXME: (extra?) all participants watched group-specifc ed- ucational videos (approx. 5 minutes total) before the experiment,

 paper: https://dl.acm.org/doi/10.1145/3544548.3580993
 """
import os, sys
# Get the absolute path of the current script's directory
current_dir = os.path.dirname(os.path.abspath(__file__))
# Get the parent directory path
parent_dir = os.path.dirname(current_dir)
# Add the parent directory to the system path
sys.path.append(parent_dir)

from z3 import *
from lib.orders import Sequence
from lib.assignment import Assignment, GroupAssignment
from lib.unit import Participants
from lib.variable import ExperimentVariable
import time as foo
from lib.blocks import BlockFactor


# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
authentication = ExperimentVariable(
    name = "authenticatioon",
    options = ["roaming", "platform"]
)

# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 

# NOTE: time-complexity is an issue here
# problem with 92 is with the number of extracted bits
subjects = Participants(89)

# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(1) 


assignment = Assignment() # identify as within-subjects design
assignment.assign_to_sequence(subjects, seq, variables = [authentication])
final = assignment.eval()

print(final)

groups = assignment.get_groups()

# NOTE: change the one so this is a constraint on participants
# do we want to make the participants as experiment variable an explicit conversion? 
participant_assignment = GroupAssignment(subjects, 1, groups)

participant_assignment.eval()
print(participant_assignment.generate_model())