from z3 import *

class Translate:
    def __init__(self):
        pass

    def different(self, left, right):
        return left != right
    
    def match(self, left, right):
        return left == right
    
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
    

    