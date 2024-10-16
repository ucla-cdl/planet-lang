from z3 import *
from itertools import product
from collections import namedtuple
import random
import itertools

# want condition to store the constraint 
# and populate the z3 vars 
# will also store the evaluation
class Condition():
    def __init__(self, *argv):
        # self.var_to_option = {}
        self.var_to_z3 = {}
        for arg in argv:
            self.var_to_z3[arg.var] = arg

        self.__z3__ = []

            # self.var_to_option[arg.var] = arg

    def eval(self):
        for var in self.var_to_z3:
            if isinstance(self.var_to_z3[var], Any):
                self.__z3__.append(self.var_to_z3[var].__z3__)
            if isinstance(self.var_to_z3[var], Z3Var):
                self.__z3__.append(self.var_to_z3[var].__z3__)
            if isinstance(self.var_to_z3[var], Different):
                self.__z3__.append(Not((self.var_to_z3[var].condition.var_to_z3[var].__z3__)))

        return self.__z3__

    # def __str__(self):
    #     ret = ""
    #     for var in self.var_to_option:
    #         ret += "option " + self.var_to_option[var].name + " from variable " + var.name  + "\n"

    #     return ret

    def __str__(self):
        return " ".join(str(key) + ": " + str(self.var_to_z3[key]) for key in self.var_to_z3)
    
    # def get_option(self, variable):
    #     return self.var_to_option[variable]
    
 

class Different:
    def __init__(self, var, condition):
        self.var = var
        self.condition = condition
        self._z3_options = condition.var_to_z3[var]
        self.__z3__ = self._z3_options.__z3__

    def __str__(self):
        return "not " + "eval of condition: " + "(" + str(self._z3_options) + ")"
    

class Match:
    def __init__(self, var, condition):
        self.var = var
        self.condition = condition
        self._z3_options = condition.var_to_z3[var]
        self.__z3__ = self._z3_options.__z3__

    def __str__(self):
        return "eval of condition: " + "(" + str(self._z3_options) + ")"

class Any:
    def __init__(self, var):
        self.var = var
        self.__z3__ = Or([option.__z3__ for option in var.conditions])

    def __str__(self): 
        return "any " + str(self.__z3__)

class Z3Var:
    def __init__(self, var, option):
        self.var = var
        self.__z3__ = var.name_to_condition[option].__z3__

    def __str__(self):
        return "must be: " + str(self.__z3__)


# named tuple
class Variable:
    def __init__(self, name, num_options, options = []):
        assert num_options == len(options) or len(options) == 0

        self.name = name
        self.n = num_options
        self.conditions = []

        self.name_to_condition = {}

        for i in range(num_options):
            attr = options[i] if len(options) > 0 else "condition" + str(i)
            option = Option(attr, self)
            self.conditions.append(option)
            setattr(self, attr, option)

        for condition in self.conditions:
            self.name_to_condition[condition.name] = condition



    # these should all return lists of options
    def any_option(self):
        print(Or([option.__z3__ for option in self.conditions]))
        return self.conditions[random.randint(0, self.n-1)]
    
    def any_test(self):
        return Any(self)
    # def match_test(self, condition)
    
    def match(self, condition):
        print(condition.get_option(self).__z3__)
        return condition.get_option(self)

    def match_test(self, condition):
        return Match(self, condition)
    
    def different(self, condition):
        print(Not(condition.get_option(self).__z3__))
        options = []
        for option in self.conditions:
            if option != condition.var_to_option[self]:
                options.append(option)
      
        return options[random.randint(0, len(options)-1)]

    def different_test(self, condition):
        return Different(self, condition)

    
    def get_option(self, option):
        # print(self.name_to_condition[option].__z3__)
        return self.name_to_condition[option]
    
    def get_test(self, option):
        return Z3Var(self, option)

    
    def __str__(self):
        return self.name

    
class Option:
    def __init__(self, name, var):
        self.var = var # reference var object that constructed this option
        self.name = name
        self.__z3__ = Bool(name)

    def __str__(self):
        return "option: " + self.name + " from variable: " + self.var.name 
    

class ConditionOrder:
    def __init__(self, n):
        # how many conditions the unit sees during the experiment
        self.n = n
        self.conditions = [None for i in range(n)]
        self.curr = 0

    def next(self, condition):
        assert self.curr < self.n
        self.conditions[self.curr] = condition
        self.curr += 1

    def eval(self):
        s = z3.Solver()
        for condition in conditions:
            s.push()
            s.add(condition.eval())
            print(s)
            s.pop()


class Units:
    def __init__(self, n):
        self.n = n

class Groups:
    def __init__(self, *argv):
        combinations = list(itertools.product(*[v.conditions for v in argv]))
    
    def conditions_per_group(self, n):
        self.n = n
    
    def order(self, order):
        self.order = order

    def create(self):
        self.order.eval()


  



# should these be user-created subclasses?
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

# should we instead pass the variables
# and then place the constraints
c1 = Condition(
    treatment.any_test(),
    task.get_test("creation")
)
c2 = Condition(
    treatment.different_test(c1), # alt = condition1.different(treatment)
    task.get_test("creation") 
)
# c3 = Condition(
#     treatment.match_test(c1), # alt = condition1.match(treatment)
#     task.get_test("editing")
# )
# c4 = Condition(
#     treatment.match_test(c2), # alt = condition2.match(treatment)
#     task.get_test("editing")
# )
conditions = [c1, c2]

order = ConditionOrder(2)

for condition in conditions:
    order.next(condition)

# order.eval()

units = Units(20)
groups = Groups(treatment, task)
# groups.conditions_per_group(order)
# groups.num_groups(4)
groups.order(order)
groups.create()
# assign(units, groups)

# assignment = Assigment(units, groups)
# assignment.assign()



# Assign(units, groups)
# ConditionOrder(totalConditions.see_exactly_one())

# order.next(condition1)
# order.next(condition2)
# order.next(condition3)
# order.next(condition4)

# group1 = order.eval()
# # gets all possible orders given the conditions 
# groups = order.eval_all()


# # assignment class, sampling class, etc... 
# # rather than just an experiment class
# Assignment(units, groups)


# order = ConditionOrder(
#     condition1, condition2, condition3, condition4,
#     all_conditions_unique=True
# )
# groups = possible_combinations(condition1, condition2, condition3, condition4, unique = True)

# assign(units, groups)


# print("1. " + str(condition1))
# print("2. " + str(condition2))
# print("3. " + str(condition3))
# print("4. " + str(condition4))


# is there a better way to formulate the SAT solver? each 
# condition var is assigned 


# variable.get_groups()
# condition_order = Order(condition1, conditon2, condition3, condition4)
# condition_order.get_groups()
# assign(units, groups)





# print(condition.treatment)


# print(treatment.conditions)