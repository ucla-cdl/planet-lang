from z3 import *
solver = z3.Solver()

# testing model for "all creation tasks come before any other task"

# tasks based on papers
# true means we choose this task 
# for current trial in block
c1 = Bool("c1")
c2 = Bool("c2")
e1 = Bool("e1")
e2 = Bool("e2")
# length of the creation list
length = Int("length")

# choose a single creation task if 
# there is a creation task available 
solver.add(Implies(length != 0, Or(c1, c2)))
solver.add(Implies(length == 0, Or(e1, e2))) 
# this is equivilant to choosing the first task 
# since there are a total of 2 creation tasks 
solver.add(length == 2)



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

    print("\n")




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


