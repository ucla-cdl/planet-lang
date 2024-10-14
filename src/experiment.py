from z3 import *
from itertools import product
from collections import namedtuple
import random
import itertools

# creates a task group, which limits you to choosing
# any variable within the given list of tasks
def create_group(tasks):
    return Or([task for task in tasks])

class Condition():
    def __init__(self, *argv):
        self.var_to_option = {}
        for arg in argv:
            self.var_to_option[arg.var] = arg

    def __str__(self):
        ret = ""
        for var in self.var_to_option:
            ret += "option " + self.var_to_option[var].name + " from variable " + var.name  + "\n"

        return ret
    
    def get_option(self, variable):
        return self.var_to_option[variable]
    
 

# named tuple
class Variable:
    def __init__(self, name, num_options, options = []):
        assert num_options == len(options) or len(options) == 0

        self.name = name
        self.n = num_options
        self.conditions = []

        for i in range(num_options):
            attr = options[i] if len(options) > 0 else "condition" + str(i)
            option = Option(attr, self)
            self.conditions.append(option)
            setattr(self, attr, option)

    def any_option(self):
        return self.conditions[random.randint(0, self.n-1)]
    
    def match(self, condition):
        return condition.get_option(self)
    
    def different(self, condition):
        options = []
        for option in self.conditions:
            if option != condition.var_to_option[self]:
                options.append(option)
      
        return options[random.randint(0, len(options)-1)]
    
    def option(self, option):
        return "must be " + str(self.c)
    
    def __str__(self):
        return self.name

    
class Option:
    def __init__(self, name, var):
        self.var = var # reference var object that constructed this option
        self.name = name

    def __str__(self):
        return "option: " + self.name + " from variable: " + self.var.name 
    

class ConditionOrder:
    def __init__(self, n):
        # how many conditions the unit sees during the experiment
        self.n = n
        self.order = [None for i in range(n)]
        self.solver = Solver()
        


    def all(self, variable, option, range=None):
        # this is equivilant to choosing the first task 
        # since there are a total of 2 creation tasks 
        if range is None:
            range = (0, self.n)

        index = Int("index")



    def conditions_match(self):
        print("conditions match constraint")
       

    def see_each_condition(self):
        print("see each condition constraint")

class Unit:
    def __init__():
        print("test")




treatment = Variable(
    name = "treatment",
    num_options = 2,
    options = ["ffl", "latex"]
)

task = Variable(
    name = "task",
    num_options = 2,
    options = ["editing", "creation"]
)


condition1 = Condition(
    treatment.any_option(),
    task.creation
)

condition2 = Condition(
    treatment.different(condition1),
    task.creation
)

condition3 = Condition(
    treatment.match(condition1),
    task.editing
)

condition4 = Condition(
    treatment.match(condition2),
    task.editing
)


# order = ConditionOrder(
#     condition1, condition2, condition3, condition4,
#     all_conditions_unique=True
# )
# groups = possible_combinations(condition1, condition2, condition3, condition4, unique = True)

# assign(units, groups)


print("1. " + str(condition1))
print("2. " + str(condition2))
print("3. " + str(condition3))
print("4. " + str(condition4))

# variable.get_groups()
# condition_order = Order(condition1, conditon2, condition3, condition4)
# condition_order.get_groups()
# assign(units, groups)





# print(condition.treatment)


# print(treatment.conditions)