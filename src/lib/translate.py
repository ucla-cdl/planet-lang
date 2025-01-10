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
        return Distinct(variables)

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
    
    def majority(self, row, val, assignments):
        return self.counts(assignments, val) > int(len(row)/2)

    def occur_exactly_n_times(self, n, num_levels, assignments):
        # store the counts for each possible level in a variable
    
        # NOTE: the stalling problem is with count!

        # check the counts of every level and check that
        # they occur exactly n times
        __z3s__ = []
        for level in range(num_levels):
            counts = self.counts(assignments, level)
            __z3s__.append((Or(counts == n, counts == 0)))

        return __z3s__
    
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
    

    

    