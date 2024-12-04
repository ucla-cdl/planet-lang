from lib.orders import PossibleOrders
from lib.assignment import Assignment
from lib.unit import Unit
from lib.variable import ExperimentVariable


# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
treatment = ExperimentVariable(
    name = "treatment",
    options = ["ffl", "latex"]
)
task = ExperimentVariable(
    name = "task",
    options = ["creation", "edit"]
)

# there are 20 units participating in the experiment
# this array holds all 20 Unit objects, and each unit
# is associated with an id (i)
units = [Unit(i) for i in range(20)] 
# given the number of conditions in an order, and all of the 
# experimental variables, create an object representing all 
# possible orders of the experimental conditions
possible_orders = PossibleOrders(4, treatment, task) 

# DIFFERENT CONSTRAINT: first and second conditions in the 
# order never have the same assignment to the treatment variable
possible_orders.different(0, 1, variable = treatment) 
# MATCH CONSTRAINT: first and third conditions in the 
# order always have the same assignment to the treatment variable
possible_orders.match(0, 2, variable = treatment)
possible_orders.match(1, 3, variable = treatment)
# FORCE CONSTRAINT: assignmnet to the task variable for 
# the first and second conditions in the order is always creation
possible_orders.force(0, variable = task, condition = "creation")
possible_orders.force(1, variable = task, condition = "creation")

# should the user have to create groups before passing to assignment?

# now the user creates an assignment object, which matches units to 
# groups, where the groups are all possible orders
assignment = Assignment(units = units, groups = possible_orders)

assignment.eval()

# assignment.unit_sees_each_condition_equal_num()
# assignment.set_num_groups(4)

# assignment.assign(units)

# assignment.assign_unit(1)



# test = ConditionTest(variable=treatment)
# print(test.variable)

# alternative to specifiying conditions



# I think it is more natural to specify dependencies like this 

# special var all
# orders.occurs_n_times(n = 1, condition=("creation", "ffl"))
# orders.num_orders = 2

# orders.occurs_once_per_index()

# example:

# # alternative to above: 
# # block = RandomBlock(4)
# order = Order(4)

# # maybe the order doesn't matter here?
# # so if we evaluate one first, add to the solver of the other
# order.different_condition(
#     0, 
#     1, 
#     variable = treatment
# )
# order.match_condition(
#     0, 
#     3, 
#     variable = treatment
# )

# order.assign_condition(
#     [0,1], 
#     condition = treatment.creation
# )

# order.assign_condition(
#     [2,3], 
#     condition = treatment.creation
# )



# assignment = Assignment( units = units,
#                          conditions_per_unit = 4,
#                          order_conditions = order,
#                 )

# # for each index in order: 
# #     apply condition to order once


# orders.order(1).isfirst(count=1)

# latin square:



# constraint on the order: 

# 1 2 3
# 2 3 1
# 3 1 2 

# 1 2 3
# 2 3 1
# 3 1 2

# 1 2 3 4
# 2 3 4 1
# 3 4 1 2
# 4 1 2 3


# 1 2 3 4
# 2 1 4 3
# 4 3 1 2
# 3 4 2 1



# # eval order 1 
# # for next unit
# #     condition 1 in order is not condition1 from order 1 
# #     condition 2 in order is not condiiton 2 in order 1 


# # order.no_condition_matches() -> no push and pop of z3 solver 
# latin square with respect to the task (e, f, c)
# c1 c2 e1 e2 f1 f2
# e1 e2 c1 c2 f1 f2
# f1 f2 e1 e2 c1 c2

# for i in range(order.n):
#     order.appears_once(index = i)



