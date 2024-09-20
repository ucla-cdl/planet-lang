\today

# Constraints for experimental designs

A trial in an experiment is represented as $(index, task)$ -- Let's ignore condition for now.

The variables are 

- set of creation tasks ($s_c$): c1, c2

- set of editing tasks ($s_e$): e1, e2

- set of group1 tasks ($s_1$): c1, e1

- set of group2 tasks ($s_2$): c2, e2

- (implied?) number of tasks = 4

The constraints for the experiment are

1. All creation tasks come before all editing tasks

Translation: 

- The index of any creation task is always less than the index of all editing tasks.

2. Every other task comes from the same grouping. 

In other words, for both the creation tasks and editing tasks, the tasks come from the same order of "group" tasks (i.e., $s_1$, $s_2$)

Translation: 

- The tasks for index 0 and 2 (computed values), must both come from $s_1$ or $s_2$. 

- If tasks for index 0 and 2 come from $s_1$, then tasks for index 1 and 3 come from $s_2$. 

- If tasks for index 0 and 2 come from $s_2$, then tasks for index 1 and 3 come from $s_1$. 


Note: To enforce internal, external validity, could generate and reason with "general" constraints -- not sure yet what these should be/look like

# Initial API idea: How to elicit from users
```sequence(task_group, task_group)```:  returns constraint

```alternate(task_group, task_group)```: returns constraint

```random(task_group)```: returns single task

# Iterating on API to support specification of constraints
GOAL: Identify composable primitives to express range of experiments. 

```r
# Specify number of each task that each participant must see
require(creation_tasks, 2)
require(editing_tasks, 2) # could later provide syntactic sugar but these seem like hard requirements

# Redundant?: 
require(group1, 2)
require(group2, 2)

# All creation tasks come before all editing tasks
sequence(creation_tasks, editing_tasks)

# For both the creation tasks and editing tasks, the tasks come from the same order of "group" tasks
## Idea 1
## Note: # Is it really "allow" or "expect/require" this sequence for all?some? participants??
allow(c1, c2, e1, e2) 
allow(c2, c1, e2, e1)

## Idea 2
# The conditions should alternate coming from group1 and group2
alternate(group1, group2) / alternate(group2, group1) -- equivalent
# If want to require group1 always starts
alternate(group1, group2, always_start_with=group1) # by default always_start_with=NULL
# OR
alternate(group1, group2)
require(group1, index=0) # index is index in ordered list of tasks
require(group1, first=TRUE) / require(group1, last=TRUE) # first and last are computed

## Other ideas
sequence(creation_tasks, editing_tasks) AND sequence(group1, group2) => UNSAT


### SCRAPS ###
# [Nope] Elements in Group1 should alternate with elements in Group2 (more like zipping) -- Too much ambiguity
# Both creation tasks must come before editing tasks
sequence(creation, editing)
# The above is shorthand for 
(c1 or c2) then (c2 or c1) then (e1 or e2) or (e2 or e1)
# Which is: 
all cs before all es

# For the creation tasks, a condtion can come from group1 or group2 first. 
# Both groups must be seen in the creation and editing tasks
# The same for the editing tasks
```

## Generally applicable constraints: 
- cannot repeat tasks
- cannot repeat exact same (task, condition) pair

## Basic boolean operations seem to be...
- before, after
- not

## Other notes
- Grouping provides syntactic sugar

## Tests: 
- groups are variable length
- compose statements
- where num_trials is neatly divisible
- Take a written out experimental design -- manually enumerated ==> synthesize a program (try this with ChatGPT?)

===
# First pass dump of ideas
```r
# DESIGN EXPL: These functions internally generate Boolean formulas?
>> WHAT DO THESE BOOLEAN FUNCTIONS LOOK LIKE?

TODO: Task and Condition should have some shared Object ancestor -- Does that mean they can share a Group function??

# First pass: Implement patterns
# 1.5 pass: Write out the logical formulae for these functions
# Second pass: Should be SAT 

# Alternate -- overloaded
# This is saying elements in tg_1 should alternate with elements in tg_2 (more like zipping)
# Edge case: What happens if num_trials does not align with experiment num_trials? => This should be a SAT prob
# This is assuming that we use all the elts passed
What if: 


alternate(3, random(2,group1), random(1, group2), random(2, group3))

Tests: 
- groups are variable length
- compose statements
- where num_trials is neatly divisible
- Take a written out experimental design -- manually enumerated ==> synthesize a program (try this with ChatGPT?)

What if num_trials is another constraint????
- how do we resolve when conditions/tasks should be repeated?


# Written with the help of ChatGPT
check_arg_types_same = function(args) {

    # Get the type of the first argument
    arg_type <- typeof(args[[1]])
    
    # Check if all arguments have the same type as the first one
    if (!all(sapply(args, typeof) == arg_type)) {
        stop("All arguments must be of the same type.")
    }

    # If all checks pass, return TRUE
    return(TRUE)
}

# Written with the help of ChatGPT
alternate = function(...) {
    # Gather all arguments into a list
    args <- list(...)
    # Check if the list is empty (no arguments passed)
    if (length(args) == 0) {
    stop("MAKE THIS MORE DESCRIPTIVE: No arguments provided. Please provide at least one argument.")
    }
    # Check all arguments are of the same type
    check_arg_types_same(args)

    
}

alternate = function(num_trials, conditions) {

}

# Sequence -- overloaded
# task1 should always come before task2
sequence = function(group1, group2, ...) {

}

sequence = function(condition1, condition2) {

}

# Random -- overloaded
random = function(tasks, num_trials) {

}

random = function(conditions, num_trials) {

}

# Part of OrderedTrials class?: 
enforce_order = function(ot, ...) {
    # need to make sure that these are SAT
}


# Future ideas
# I find myself drawing the squares/table in my mind --> Maybe we could provide different visualization functions?

# get a high-level rule or example and synthesize rules for controlling order
custom = function (example) {

}
```
