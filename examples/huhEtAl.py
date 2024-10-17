# Date: Oct 17
# Author: Eunice Jun
# Example program for Huh et al. UIST 2023 paper (https://dl.acm.org/doi/pdf/10.1145/3586183.3606735)


# import <library name>

interface = ExperimentVariable(
    name = "interface",
    options = ["GenAssist", "baseline"]
)

short_prompts = ExperimentVariable(
    name = "short prompts",
    options = ["s1", "s3"]
)

long_prompts = ExperimentVariable(
    name = "long prompts",
    options = ["s2", "s4"]
)

interp_task = ExperimentVariable()

short_task = ExperimentVariable(
    name = "short interpretation task", 
    options = ["s1", "s3"]
)

long_task = ExperimentVariable(
    name = "long interpretation task", 
    options = ["s2", "s4"]
)

# This doesn't make sense since there are so many details about each kind of task
# task = ExperimentVariable(
#     name = "task", 
#     options = ["interpretation", "generation"]
# )

"""
For each interface, users were given one
short prompt image set (S1 or S3) and one long prompt image
set (S2 or S4). The order of the interfaces and image sets were
counterbalanced and randomly assigned to participants.

Notes: 
- counterbalanced across participants --> need constraints across participants (e.g., also for a Latin Square)
- possible confounder: the images involved in long prompts were more similar to each other than images involved in short prompts, which were less similar/more dissimilar
"""
short_cond = ExperimentCondition(
    interface.any()
    short_task.any()
)
long_cond = ExperimentCondition(
    interface.different(short_cond)
    long_task.any()
)

# I want to say that the order of the conditions can be random but the interfaces need to be different
HOW??
What if: 
short_cond = ExperimentCondition(
    interface = interface.any() # Nothing inherent about this condition -- i.e., requirement for how to pair interface and task
    task = short_task.any()
)
long_cond = ExperimentCondition(
    interface = interface.any()
    task = long_task.any()
)
RandomOrder(short_cond, long_cond) # Doesn't matter which comes first
different(short_cond.interface, long_cond.interface)
