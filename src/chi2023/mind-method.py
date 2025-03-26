""" The design: 

 Participants were randomly assigned to one of four conditions in a 2x2 between-subjects design. The two independent variables were (1) the regulatory mode (assessment vs. locomotion) the companion induced and (2) the decision strategy (full evaluation vs. progres- sive elimination) the companion supported.

 paper: https://dl.acm.org/doi/10.1145/3544548.3581529

 FIXME: 9! is approx 300,000, so this takes a long time to terminate...
 probably why they psuedo randomize with a partially counterbalanced study 
 currently, we do not support any of these soft constraints, but they seem important for validating designs
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

# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
strategy = ExperimentVariable(
    name = "strategy",
    options = ["progressive elim", "full eval"]
)
mode = ExperimentVariable(
    name = "mode",
    options = ["assesment", "locomotion"]
)

# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
# subjects = [Subject(i+1) for i in range(2)] 

# problem with 92 is with the number of extracted bits
subjects = Participants(81)

# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
seq = Sequence(1) 


assignment = Assignment() # identify as within-subjects design
assignment.assign_to_sequence(subjects, seq, variables = [strategy, mode])
final = assignment.eval()

print(final)

groups = assignment.get_groups()

# NOTE: change the one so this is a constraint on participants
# do we want to make the participants as experiment variable an explicit conversion? 
participant_assignment = GroupAssignment(subjects, 1, groups)

participant_assignment.eval()
print(participant_assignment.generate_model())