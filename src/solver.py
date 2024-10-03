from z3 import *
solver = z3.Solver()

# note: enforce only pick one, so (c1 and not(c2 or c3 or c4), 
# (c2 and not(c1 or e1 or e2)), etc...


# testing model for "all creation tasks come before any other task"
# tasks based on papers
# true means we choose this task 
# for current trial in block
c1 = Bool("c1")
c2 = Bool("c2")
e1 = Bool("e1")
e2 = Bool("e2")

def create_group(tasks):
    return Or([task for task in tasks])

creation = create_group((c1, c2))

tasks = (c1, c2, e1, e2)
# length of the creation list
seen_all_creation = Bool("seen_all_creation")

def get_other_tasks(task):
    return [other_task for other_task in tasks if not (other_task == task)]

# this enforces that we can only have one satisfying variable 
# (because we can only put one variable in each block)
# example of enforcing one pick: c1 and not(c2 or c3 or c4)
block = []
# for task in tasks: 
for task in tasks: 
    other_tasks = get_other_tasks(task)
    block.append(And(task, Not(Or(other_tasks))))

solver.add(Or(block))

# choose a single creation task if 
# there is a creation task available 
solver.add(Implies(seen_all_creation == True, creation))
solver.add(Implies(seen_all_creation == False, Not(creation))) 
# this is equivilant to choosing the first task 
# since there are a total of 2 creation tasks 
solver.add(seen_all_creation==False)


# constraint with respect to a block
# if not seen_all_creation, then (group1 or group2)
# if seen(group1) then group2
# if seen(group2) then group1

# while the constraints are satisfiable 
while (solver.check() == sat):
    model = solver.model()
    # satifing variables
    print(model)

    block = [] # constraints to add
    for var in model:
        # variable does not equal it's current value
        block.append(var() != model[var])

    # add constraints so we pick a new var
    solver.add(Or(block))
    print(block)
    print("\n")


# IDEA: 2 models, where m1 gives possibilities for individual entities,
# and m2 which checks SAT over all individual entities in a block

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

# if groups = # conditions