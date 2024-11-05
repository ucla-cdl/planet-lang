from .condition import ConditionTest
from .helpers import DEBUG
from z3 import *
import numpy as np

# this is a helper function
def add(list, exp, n):
    if n == 1:
        exp = list[0]
        return exp

    exp = list[n - 1] + list[n - 2]
    list[n - 2] = exp
    return add(list, exp, n-1)

class PossibleOrders:
    """The PossibleOrders class represents all of the possible
        orders of conditions in an experiment, where each order
        is an experimental group

    n: the number of conditions in each order
    we use argv so the user can pass any number of variables
    because experiments have varying amount of variables
    """
    def __init__(self, n, *argv):
        self.n = n
        self.order = [None for _ in range(n)]
        self.curr = 0
    
        for _ in range(n-1):
            self.add(ConditionTest(argv))

        self.curr = 0
        self.solver = z3.Solver()
        self.variables = []

        self.z3_vectors = {}

        for arg in argv:
            self.variables.append(arg)

            self.z3_vectors[arg] = [Int(f"{str(arg)}_{index + 1}") for index in range(n)]

            k = len(arg.conditions)

            self.solver.add([And(1 <= self.z3_vectors[arg][index], k >= self.z3_vectors[arg][index]) for index in range(n)])
        

        # same for all any variables
        self.combined_conditions = [Int(f"C_{index + 1}") for index in range(n)]
        self.solver.add([Distinct(self.combined_conditions)])

        for i in range(n):
            count = len(self.z3_vectors)-1
            test = []
            for var in self.z3_vectors:
                exp = self.z3_vectors[var][i] * 10**count
                test.append(exp)
                count -= 1

            exp = add(test, None, len(test))
            self.solver.add(self.combined_conditions[i] == exp)

        self.all_orders = []



    def add(self, condition):
        condition.add_name("condition" + str(self.curr+1))
        self.order[self.curr] = condition
        self.curr += 1

    def different(self, i1, i2, variable):
        self.solver.add(self.z3_vectors[variable][i1] != self.z3_vectors[variable][i2])

    def match(self, i1, i2, variable):
        self.solver.add(self.z3_vectors[variable][i1] == self.z3_vectors[variable][i2])


    # not finished (need a mapping of indices to variable assignments)
    def force(self, i, variable, condition):
        val = 0

        # probably somethign more efficient... do we want to store 
        # these mappings, so we dont have to comput every time and then loop?
        # reasoning not to is that no variable should have many conditions
        condition_names = list(map(lambda condition: condition.name, variable.conditions))

        for c in condition_names:
            if c == condition:
                val = condition_names.index(c) + 1

        self.solver.add(self.z3_vectors[variable][i] == val)
   
    # get a specific ordering given constraints
    def eval(self):
        while self.solver.check() == sat:
            model = self.solver.model()

            block = []
            order = []
            for var in self.combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            self.all_orders.append(order)
      

            self.solver.add(Or(block))

        orders = []
        for i in range(len(self.all_orders)):
            order = []
            for j in range(len(self.all_orders[0])):
                # efficiently get first elem?
                var = ""
                for v in range(len(self.variables)):

                    x = int(str(self.all_orders[i][j])[v])-1
                    var+=str(self.variables[v].conditions[x])
                    if v < len(self.variables)-1:
                        var+="-"
                order.append(var)
           
            orders.append(order)
        
        
        return orders

class Groups(PossibleOrders):
    def __init__(self, *argv):
        super().__init__(1, *argv)


class Sequence:
   
    def __init__(self, n):
        self.n = n
        self.sequence = [None for _ in range(n)]

        self.solver = z3.Solver()
        self.variables = []

        self.z3_vectors = {}

        for arg in argv:
            self.variables.append(arg)

            self.z3_vectors[arg] = [Int(f"{str(arg)}_{index + 1}") for index in range(n)]

            k = len(arg.conditions)

            self.solver.add([And(1 <= self.z3_vectors[arg][index], k >= self.z3_vectors[arg][index]) for index in range(n)])
        

        # same for all any variables
        self.combined_conditions = [Int(f"C_{index + 1}") for index in range(n)]
        self.solver.add([Distinct(self.combined_conditions)])

        for i in range(n):
            count = len(self.z3_vectors)-1
            test = []
            for var in self.z3_vectors:
                exp = self.z3_vectors[var][i] * 10**count
                test.append(exp)
                count -= 1

            exp = add(test, None, len(test))
            self.solver.add(self.combined_conditions[i] == exp)

        self.all_orders = []



    def add(self, condition):
        condition.add_name("condition" + str(self.curr+1))
        self.order[self.curr] = condition
        self.curr += 1

    def different(self, i1, i2, variable):
        self.solver.add(self.z3_vectors[variable][i1] != self.z3_vectors[variable][i2])

    def match(self, i1, i2, variable):
        self.solver.add(self.z3_vectors[variable][i1] == self.z3_vectors[variable][i2])


    # not finished (need a mapping of indices to variable assignments)
    def force(self, i, variable, condition):
        val = 0

        # probably somethign more efficient... do we want to store 
        # these mappings, so we dont have to comput every time and then loop?
        # reasoning not to is that no variable should have many conditions
        condition_names = list(map(lambda condition: condition.name, variable.conditions))

        for c in condition_names:
            if c == condition:
                val = condition_names.index(c) + 1

        self.solver.add(self.z3_vectors[variable][i] == val)
   
    # get a specific ordering given constraints
    def eval(self):
        while self.solver.check() == sat:
            model = self.solver.model()

            block = []
            order = []
            for var in self.combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            self.all_orders.append(order)
      

            self.solver.add(Or(block))

        orders = []
        for i in range(len(self.all_orders)):
            order = []
            for j in range(len(self.all_orders[0])):
                # efficiently get first elem?
                var = ""
                for v in range(len(self.variables)):

                    x = int(str(self.all_orders[i][j])[v])-1
                    var+=str(self.variables[v].conditions[x])
                    if v < len(self.variables)-1:
                        var+="-"
                order.append(var)
           
            orders.append(order)
        
        
        return orders





    
