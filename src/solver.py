from z3 import *
solver = z3.Solver()

# creates a task group, which limits you to choosing
# any variable within the given list of tasks
def create_group(tasks):
    return Or([task for task in tasks])

# returns array of all tasks not including the task passed
def get_other_tasks(task, tasks):
    return [other_task for other_task in tasks if not (other_task == task)]

def force_pick_one(tasks):
    # this enforces that we can only have one satisfying variable 
    # (because we can only put one variable in each block)
    # example of enforcing one pick: c1 and not(c2 or c3 or c4)
    block = []
    # for task in tasks: 
    for task in tasks: 
        other_tasks = get_other_tasks(task, tasks)
        block.append(
            And(
                task, 
                Not(Or(other_tasks))
            )
        )   

    return Or(block)

# given list of Task objects, convert to z3 Bool object
# returns map of Task object to z3 object
def vars_to_z3(vars):
    map_vars_to_z3 = {}
    for var in vars:
        map_vars_to_z3[var] = Bool(var)

    return map_vars_to_z3

# choose a single creation task if 
# there is a creation task available 
def constraint_all_share_condition(seg_index, condition_group):
    # this is equivilant to choosing the first task 
    # since there are a total of 2 creation tasks 
    solver.add(Implies(seg == seg_index, condition_group))
    solver.add(Implies(seg != seg_index, Not(condition_group))) 
   

solver = z3.Solver()
# note: enforce only pick one, so (c1 and not(c2 or c3 or c4), 
# (c2 and not(c1 or e1 or e2)), etc...

# testing model for "all creation tasks come before any other task"
# tasks based on papers
# true means we choose this task v
# for current trial in block

# TODO: construct using task to z3
c1 = Bool("c1")
c2 = Bool("c2")
e1 = Bool("e1")
e2 = Bool("e2")

# get these from R objects
dsl_vars = []

# these should be automatically constructed based on constraints
creation = create_group((c1, c2))
g1 = create_group((c1, e1))
g2 = create_group((c2, e2))
tasks = (c1, c2, e1, e2)
# what does it mean to be in a group?
# c1 in g1 if c1 == True sat Or(c1, c2)
# shares_group(t1, t2, list(groups...))

# length of the creation list
seg = Int("seg") # based on segment constraint

def segment_conditions(num_segments):
    solver.add(seg > 0, seg <= num_segments)

solver.add(force_pick_one(tasks))

# constructs z3 bools indicating if a certain task 
# shares a condition with the group specified 
def construct_match_variables(variable, num_conditions_in_variable):
    var_to_z3 = {}
    for j in range(1,num_conditions_in_variable+1):
        var_to_z3[variable + str(j)] = Bool(variable + str(j))

    return var_to_z3


# to complete this we need a notion of index
def match_order_from_segment(seg_index):
    
    task_in_group = construct_match_variables("task", 2)
    print(task_in_group)
    solver.add(Implies( 
            seg != seg_index,
            force_pick_one([task_in_group[test] for test in task_in_group])
            )
    )

    g = None
    for group in task_in_group:
        if group == "task0":
            g = g1
        elif group == "task1":
            g = g2

        solver.add(Implies(
                    And(
                        task_in_group[group] == True,
                        seg != seg_index
                    ),
                    g
                )
            )

# alternate model idea: set task condition variables, 
# not variables on the combinations
constraint_all_share_condition(1, creation)
match_order_from_segment(1)
segment_conditions(2)


# constraint with respect to a block
# if not seen_all_creation, then (group1 or group2)
# if seen(group1) then group2
# if seen(group2) then group1

# for testing:
# solver.add(t1_in_group["g2"] == True)
solver.push()
solver.add(seg == 1)
seg_val = 1
# while the constraints are satisfiable 
while (solver.check() == sat):
    print("Model possibility for a condition in segment", seg_val)
    model = solver.model()
    # satifing variables
    print(model)
    solver.pop()
    
    block = [] # constraints to add
    for var in model:
        # variable does not equal it's current value
        if model[var] == True and var != seg:
            block.append(var() != True)
            

    # add constraints so we pick a new var
    solver.add(Or(block))

    # ugly - ignore this
    solver.push()
    solver.add(seg == seg_val)
    if solver.check() != sat:
        solver.pop()
        solver.push()
        seg_val += 1
        solver.add(seg == seg_val)

    print("\n")

    # NO repeat is explicit
    # number conditions per unit (for each task)
    # total and with resprect to each variable
    # the user does not know how many conditions (give output)
    # global set of conditions defined as combination of tasks
    # outut all options
    # alternitive specificistion ? to all and pick one 
    # explicit unit object: assign unit any(sleep)
    # assign on confiditon to unit of type(type)
    # unit gets one condition(1, type)
    # get_condition -> selct_random
    # all(one of tasks type)
    # specify which task to pull condition from for all constraints
    # segments_see_same_order(segment1, segment2) -> come up with order 
    # next step: given example programs -> try latin square 
    # start the changes, prioritize... be clear on purpose 
    # strip down examples into core statements...
    # each program has unique core  (core primitives!)

    ## TALK ABOUT GOALS***

 




# IDEA: 2 models, where m1 gives possibilities for individual entities,
# and m2 which checks SAT over all individual entities in a block

# second model could represent which group a task comes from...
# in group 1?
#   Implies c1 or e1, then task_in_group[1]
#   Implies c2 or e2, then task_in_group[2]

# then set first model var task_in_group[i] to true and check model


# examples: m1 returns (c1 == True , c2 == True)

# m2 checks for at least one group 1 (c1 or e1) AND at least one group 2 (c2 or e2)
# this is sat, so we keep this option.

# fails if we recieve (c1 = True, c1 = True)
# because not(c2 or e2)

# axioms

# within experiment
'''
task-condition combo appears in ONE column 
a column represents a task-condition pair 
a row is a group that a unit gets assigned to 
a unit must be assigned to all task-condition pairs 
we must see all possible orderings of conditions 
'''

# note: rather than represent a task var as a bool,
# represent as number where the value is the location 
# experimental design matrix ?

# c1.loc() == 1



# between experiment
'''
each unit sees one task-condition combo 
there are n groups where n is the number of task-condition pairs 
we see every task-condition combo 
'''

'''
testing for paper results
'''

# if # groups = # conditions, then btw. unit
# if len(block) == 1