# %%
# 🛰️ Welcome to PLanet!

# This tutorial walks you through defining experimental designs using PLanet.
# Run each cell with Shift+Enter. Modify code to experiment with different setups.

# Let's begin by defining a variable.
from planet import ExperimentVariable, Design, Units, assign, nest

interface = ExperimentVariable("interface", options=["baseline", "VR", "AR"])
interface

# %%
# Now let's construct a between-subjects design with this variable.

design = (
    Design()
        .between_subjects(interface)
)

# %%
# Let's simulate recruiting 12 participants.

units = Units(12)

# %%
# Now assign conditions to participants.

assignment = assign(units, design)
assignment.pretty_print()  # if supported

# %%
# Now let's create a within-subjects design instead.

design = (
    Design()
        .within_subjects(interface)
)

# %%
# By default, each participant gets all conditions. Let's try 2 trials per unit.

design = (
    Design()
        .within_subjects(interface)
        .num_trials(2)
)

# %%
# Assign and print plans

assignment = assign(units, design)
assignment.pretty_print()

# %%
# The trial orders may repeat. Let's add counterbalancing.

design = (
    Design()
        .within_subjects(interface)
        .num_trials(2)
        .counterbalance(interface)
)

assignment = assign(units, design)
assignment.pretty_print()

# %%
# Define a new variable: task

task = ExperimentVariable(
    name="task",
    options=["run", "walk", "sprint"]
)

task_design = (
    Design()
        .within_subjects(task)
)

# %%
# Add counterbalancing to make it a Latin square

task_design = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)

assignment = assign(units, task_design)
assignment.pretty_print()

# %%
# There are 6 possible orders. To get a Latin square, we must limit plans to 3.

task_design = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
        .limit_plans(len(task))  # 3
)

assignment = assign(units, task_design)
assignment.pretty_print()

# %%
# Combine both designs by nesting the task design inside the interface design

interface_design = (
    Design()
        .within_subjects(interface)
        .counterbalance(interface)
)

combined_design = nest(inner=task_design, outer=interface_design)

assignment = assign(units, combined_design)
assignment.pretty_print()

# %%
# The design may require more participants to satisfy counterbalancing
# Check for dropouts (pid = -1)

# You can increase the number of units to avoid dropouts:
units = Units(24)
assignment = assign(units, combined_design)
assignment.pretty_print()

# %%
# Optional: force every plan to begin with a baseline interface

# (Assumes you have a method like .start_with("baseline"))
# This is pseudocode unless your API supports it:
# interface_design = interface_design.start_with("baseline")

# %%
# ✅ You're ready!

# Feel free to modify any of the designs above or define your own.
# Happy designing!
