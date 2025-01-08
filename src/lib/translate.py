from z3 import *
from .candl import *

class Translate:
    def __init__(self):
        pass

    def different(self, left, right):
        return left != right
    
    def match(self, left, right):
        return left == right
    
    def conditional(self, left, right):
        return Implies(left, right)
    
    def all_different(self, variables):
        self.solver.add(Distinct(variables))

    def check_match(self, val, x):
        return If(val == x, 1, 0)
    
   
    
    def occur_together(self, val1, val2, row1, row2, f):

        # FIXME: the array without the values we check for equality 
        arr1 = row1[:]
        arr1.pop(arr1.index(val1))
        arr2 = row2[:]
        arr2.pop(arr2.index(val2))

        # if two variables are equal, no values in their 
        # respective rows can be equal 
        __z3__ = self.conditional(
                    self.match(val1, val2), 
                    f(arr1, arr2)
                )

        return __z3__
        

    def counts(self, l, x):

        test = []
        for val in l: 
            # I really want to optimize this so we can reuse the lo and high values 
            test.append(self.check_match(val, x))

        return sum(test)
    
    # FIXME: but, I think this should be wrt a variable?
    def no_values_match(self, arr1, arr2):
        constraints = []
        for val1 in arr1:
            for val2 in arr2:
                constraints.append( val1 != val2)
        return And(constraints)
    

    def values_match(self, arr1, arr2):
        constraints = []
        for i in range(len(arr1)):
            constraints.append(arr1[i] == arr2[i])
    
        return And(constraints)
    
    def majority(self, block, num_levels, val, var):
        g = Function("g", IntSort(), IntSort(), IntSort(), IntSort())

        # NOTE: the stalling problem is with count!
        # check the counts of every level and check that
        # they occur exactly n times
        counts = []
        

        for row in block:
            for x in range(num_levels):
                for j in range(len(block)):
                    self.solver.add(g(j, x, val) == self.counts(block[j], x, var))

                    if x == val:
                        self.solver.add(g(j, val, val) > int(len(row)/2))
    
    def occur_exactly_n_times(self, n, variable, variables):
        if n == 1:
            self.all_different()

        else: 
            # store the counts for each possible level in a variable
            num_levels = len(variable)
            f = Function("f", IntSort(), IntSort())

            # NOTE: the stalling problem is with count!

            # check the counts of every level and check that
            # they occur exactly n times
            for level in range(0, num_levels):
                count(variables, level, variable)
                self.solver.add(f(level) == self.count(variables, level, variable))
                self.solver.add(Or(f(level) == n, f(level) == 0))
    
    # works when z3 representation is a matrix 
    def get_one_model(self, combined_conditions, solver):
        all_assignments = []

        if (solver.check() == sat):
            model = solver.model()

            for var in combined_conditions:
                all_assignments.append(model.evaluate(model[var]))

        return all_assignments
    
    # works when z3 rep iterates through many arrays
    # NOTE: should I merge these two functions?
    def get_all_models(self, combined_conditions, solver):
 
        all_orders = []
        solver.push()

        while solver.check() == sat:
            model = solver.model()

            block = []
            order = []
            for var in combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            all_orders.append(order)
            solver.add(Or(block))

        solver.pop()
        return all_orders
    

    

    