from z3 import *
from itertools import product
import random
import itertools

# creates a task group, which limits you to choosing
# any variable within the given list of tasks
def create_group(tasks):
    return Or([task for task in tasks])

seg = Int("seg")
class Experiment:

    def __init__(self):
        self.variables = []
        self.conditions = []
        self.groups = {} # num groups is num conditions (2 x 2 x 2 for example)
        self.conditions_per_unit = 1
        self.num_segments = 1
        self.segment_length = 1

    def create_var(self, name, n, conditions=[]):
        self.variables.append(Variable(name, n, conditions))

    def construct_conditions(self):
        combinations = list(itertools.product(*[v.conditions for v in self.variables]))
        self.conditions = [Condition(combination) for combination in combinations]

    def num_conditions_per_unit(self, n):
        self.conditions_per_unit = n

    def segment(self, n):
        assert self.conditions_per_unit % n == 0
        self.num_segments = n
        self.segment_length = int(self.conditions_per_unit/n)

    def construct_groups(self):
        ## terribly ugly 
        for condition in self.conditions:
            for var in self.variables:
                for subc in var.conditions:
                    if subc in condition.subconditions:
                        if subc in self.groups:
                            self.groups[subc].append(condition)
                        else:
                            self.groups[subc] = []
                            self.groups[subc].append(condition)

# named tuple
class Variable:
    def __init__(self, name, n, conditions):
        self.name = name
        self.n = n

        assert n == len(conditions) or len(conditions) == 0

        if len(conditions) == 0:
            self.conditions = [str(i) for i in range(1, n+1)]
        else:
            self.conditions = conditions

    def __str__(self):
        return self.name
    
class Condition():
    def __init__(self, subconditions):
        self.subconditions = subconditions
        self.name = "".join(subconditions)
        self.__z3__ = self.construct_z3_var()


    def construct_z3_var(self):
        return Bool(self.name)
  


e = Experiment()
e.create_var("task-type", 2, conditions=["e", "c"])
e.create_var("treatment", 2, conditions = ["f", "l"])
e.create_var("task-index", 2)
e.num_conditions_per_unit(4)
e.segment(2)


# testing
# assignment
# e = Experiment()
# treatment = Var("treatment")
# task = Var("task")
# unit = Unit()
# unit.num_conditions_seen(4)


# for condition_thing in unit_conditions: 
#     unit.sees_once(condition_thing)
#     condition_thing.force(treatment1, "treatment1")
#     if condition_thing in first half: 
#         condition_thing.force_task(creation)

# # miniize need for segments
# condition1.lookslike(condition2)
# condition2.different_from(condition1)

# experiment.pass_order(order)



# internal use
e.construct_conditions()
e.construct_groups()

ffl = [condition.__z3__ for condition in e.groups["f"]]
latex = [condition.__z3__ for condition in e.groups["l"]]
group1 = [condition.__z3__ for condition in e.groups["1"]]
group2 = [condition.__z3__ for condition in e.groups["2"]]
creation = [condition.__z3__ for condition in e.groups["c"]]
editing = [condition.__z3__ for condition in e.groups["e"]]
creation = create_group(creation)
editing = create_group(editing)
g1 = create_group(group1)
g2 = create_group(group2)
l = create_group(latex)
f = create_group(ffl)
tasks = [c.__z3__ for c in e.conditions]



solver = z3.Solver()

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

    assert solver.check() == sat
    # print(solver.model())
   

def segment_conditions(num_segments):
    solver.add(seg > 0, seg <= num_segments)

# constructs z3 bools indicating if a certain task 
# shares a condition with the group specified 
def construct_match_variables(variable, num_conditions_in_variable):
    var_to_z3 = {}
    for j in range(1, num_conditions_in_variable+1):
        var_to_z3[variable + str(j)] = Bool(variable + str(j))

    return var_to_z3


unit_order = []
def pick_random(unit_conditions, i, solver):
    index = random.randrange(0, len(unit_conditions[i]))
    unit_order.append(unit_conditions[i][index][1]())
    solver.add(unit_conditions[i][index][1]() != True)


seg = Int("seg")
# this needs to be stored in a class
condition_to_group = {"treatment1":l, "treatment2":f, "task1":g1, "task2":g2}
# to complete this we need a notion of index
def match_order_from_segment(seg_index, variable):
    global match_order
    match_order = True
    solver.add(
        Implies( 
            seg != seg_index,
            force_pick_one(
                [variable[condition] for condition in variable]
            )
        )
    )

    for condition in variable:
        g = condition_to_group[condition]

        solver.add(
            Implies(
                And(
                    variable[condition] == True,
                    seg != seg_index
                ),
                g
            )
        )

def segment_sees_each_condition(segment, variable):
    global sees_all
    sees_all = True

# BELOW ARE THE CONSTRAINTS
# alternate model idea: set task condition variables, 
# not variables on the combinations
# what if we wanted multiple segments?
task_in_group = construct_match_variables("task", 2)
treatment_in_group = construct_match_variables("treatment", 2)
match_order = False
sees_all = False









# SETTING THE CONSTRAINTS
segment_conditions(e.num_segments)
constraint_all_share_condition(1, creation)
# constraint_all_share_condition(1, editing)
match_order_from_segment(1, task_in_group)
match_order_from_segment(1, treatment_in_group)
segment_sees_each_condition(1, "treatment")
segment_sees_each_condition(1, "task-index")















index_var = {1:group1, 2:group2}
condition_var = {1: ffl, 2: latex}

def create_solver(num_conditions_per_unit):

    solver.add(force_pick_one(tasks))
    # the order of conditions we return to the user 
    conditions = [[] for i in range(num_conditions_per_unit)]

    for i in range(num_conditions_per_unit):
        solver.push() # save state for next index
        seg_val = 1 # chnage this to loop through each segment

        # need to generalize this if more than two segments
        if i >= e.segment_length:
            seg_val = 2
        
        # assert which segment we are in
        solver.add(seg == seg_val)
        
        # note: below is pass 2 of solver
        #  (we can't know these constraints statically)
        # when this grows we will need a pop notion for 
        # segment level AND for task level
        # right now we just have task-level stack ops

        # this needs to be a function!!!!!
        # represent this as lambda function that we set based on constraint?
        if match_order and i >= e.segment_length: 
            if unit_order[i-e.segment_length] in group1:
                solver.add(task_in_group["task1"] == True)
            elif unit_order[i-e.segment_length] in group2:
                solver.add(task_in_group["task2"] == True)

            if unit_order[i-e.segment_length] in latex:
                solver.add(treatment_in_group["treatment1"] == True)
            elif unit_order[i-e.segment_length] in ffl:
                solver.add(treatment_in_group["treatment2"] == True)

        # THIS NEEDS TO BE IT'S OWN FUNCTION
        # GENERALIZE FOR ANY VARIABLES
        if i == 1 and sees_all:
            if unit_order[0] in group1:
                solver.add(Not(g1))
            if unit_order[0] in group2:
                solver.add(Not(g2))

            if unit_order[0] in latex:
                solver.add(Not(l))
            if unit_order[0] in ffl:
                solver.add(Not(f))

        # while the constraints are satisfiable 
        while (solver.check() == sat):
            model = solver.model()

            block = [] # constraints to add
            for var in model:
                # variable does not equal it's current value
                if model[var] == True:
                    block.append(var() != True)
                    # the var is true if this satisfies the constraint for this index
                    if var() in tasks:
                        conditions[i].append((model, var))
                    

            # We never want to see this combination for this index
            solver.add(Or(block))
        
        # constraints don't apply for next index
        solver.pop()

        # We did not generate any models
        if (solver.check() != sat):
            raise Exception("No possible orderings given constraint")
        else:
            # this picks a random variable for this index
            pick_random(conditions, i, solver)

        

    print(unit_order)
    
create_solver(e.conditions_per_unit)


# Is this faster than just pruning ???
# space complexity is less because we don't 
# need to store all possible orders

# notes from 10/08
# number conditions per unit (for each task)
# total and with resprect to each variable
# the user does not know how many conditions (give output)
# global set of conditions defined as combination of tasks
# outut all options

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


# just for testing - ignore for now
def test_all():
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




# segments = {}

# for i in range(e.num_segments):
#     segments[i] = []

# for i in range(e.num_segments):
#     for j in range(e.segment_length):
#         segments[i].append(j + i*e.segment_length)
# we want to incorporate this to main solver 
# check incrementally? z3 array type?


def solver_on_array(unit_conditions, variable):
    n = len(unit_conditions)

    map_to_type = {}
    for condition in unit_conditions:
        for option in variable:
            # make these solver constraints
            if condition in variable[option]:
                map_to_type[condition] = option
    
    order = [None for i in range(n)]
    for i in range(n):
        order[i] = Int(str(i))
        s.add(order[i] == map_to_type[unit_conditions[i]])

    m = len(segments)
    for i in range(m):
        s.add(order[i] == order[i + len(segments[0])])

    if (s.check() == sat):  
        return unit_conditions
    else:
        print("Segments do not match")

