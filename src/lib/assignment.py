from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .variable import ExperimentVariable

class Assignment:
    """The assignment class matches each unit to an order of conditions.

    units: a list of unit objects 
    conditions_per_unit: how many experimental conditions does each unit witness/experience
    possible_orders: an object that maintains information about the possible 
        orderings of experimental condiitons, and the user-defined constraints
        on which conditions must/can appear in different positions in the order
    """
    def __init__(self, units = None, groups = None):
        self.units = units

        self.unit_options = None
        self.treatments = None
        self.unit_variables = []
        self.constraints = []

        # reason for implementing constraint objects
        self.test = False

    def assign_to_sequence(self, subjects, sequence):
        dims = [subjects.n, sequence.n]
        self.unit_variables = [subjects, sequence]

        # block factors should be rows

        # maybe we construct these post-constraints
        # so that the dimensions only include those that 
        # have constraints. Otherwise we will construct all :)
        matrix = add_dimension(dims, self.unit_variables)
        matrix = construct_units(matrix, dims)
        matrix = construct_z3(matrix, dims)

        self.units = matrix

    def compose_conditions(self, treatment):
        self.treatment = treatment
        symbols = len(treatment.conditions)
     
        r = len(self.units)
        c = len(self.units[0])
        if self.units != None:
            self.unit_options = [And(1 <= self.units[i][j], symbols >= self.units[i][j]) for i in range(r) for j in range(c)]

    # ensure that we distinguish this
    def recieve_different_conditions(self, block):
        r = self.unit_variables[0]
        c = self.unit_variables[1]

        if block == r:  
            print(block)
            self.test = True


        if block == r:
            n = c.n
        else:
            n = r.n

        # when we add another constraint, add dim?

        for i in range(n):
            if block == r:
                arr = [self.units[j][i] for j in range(block.n)]
            if block == c:
                arr = [self.units[i][j] for j in range(block.n)]
             
            self.constraints.append(Distinct(arr))

        # I want this instead to return a constraint condition :)
        

    def constrain_z3_values(self, seq):
        for variable in seq.variables:
            seq.solver.add([And(1 <= seq.z3_vectors[variable][index], variable.n >= seq.z3_vectors[variable][index]) for index in range(seq.sequence_length)])


    def create_z3_for_conditions(self, seq):
        # same for all any variables
        return [Int(f"C_{index + 1}") for index in range(seq.sequence_length)]
    
    # conditions are a combination of variable assignments
    def constrain_z3_conditions(self, seq, combined_conditions):
        for i in range(seq.sequence_length):
            count = len(seq.z3_vectors)-1
            test = []
            for var in seq.z3_vectors:
                exp = seq.z3_vectors[var][i] * 10**count
                test.append(exp)
                count -= 1

            exp = add(test, None, len(test))

            seq.solver.add(combined_conditions[i] == exp)


    def get_all_models(self, seq, units, combined_conditions):
        count = 0
        while seq.solver.check() == sat and count < units.n:
            model = seq.solver.model()

            block = []
            order = []
            for var in combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            seq.all_orders.append(order)
      

            seq.solver.add(Or(block))
            count += 1

    # probably should just be a class
    def encoding_to_name(self, seq):
        orders = []
        r = len(seq.all_orders)
        c = len(seq.all_orders[0])
        num_vars = len(seq.variables)
        for i in range(r):
            order = []
            for j in range(c):
                # efficiently get first elem?
                var = ""
        
                for v in range(num_vars):
                    x = int(str(seq.all_orders[i][j])[v])-1
                    var+=str(seq.variables[v].conditions[x])
                    if v < len(seq.variables)-1:
                        var+="-"
                order.append(var)
           
            orders.append(order)

        return orders


    # somehow merge eval and generate
    def eval(self):
        units = self.unit_variables[0]
        seq = self.unit_variables[1]

        assert isinstance(seq, Sequence)

        # ok, so we know we can postpone the eval of this 
        # why am I passing a class-variable?
        seq.construct_z3_variable(seq.variables)
        # do the loop in seq though
        for constraint in seq.constraints:
            seq.eval_constraint(constraint)

        

        self.constrain_z3_values(seq)
        combined_conditions = self.create_z3_for_conditions(seq)
        seq.solver.add([Distinct(combined_conditions)])
        
        self.constrain_z3_conditions(seq, combined_conditions)

        print(seq.solver)

        self.get_all_models(seq, units, combined_conditions)

   

      


        return self.encoding_to_name(seq)
    
    def generate(self):

        if self.test:
            s = z3.Solver()
            r = self.unit_variables[0].n
            c = self.unit_variables[1].n


            for i in range(r):
                for j in range(r):
                    if i == j:
                        continue
                    arr = [self.units[i][k] != self.units[j][k] for k in range(c)]
                    s.add(Or(arr))
            
            # something here is not working
            # the indices are a bit odd... need to compare to play file


            s.add(self.unit_options + self.constraints)

            print("running with constraints")
            if (s.check() == sat):
                model = s.model()
                print("done running")
                return np.matrix([[model[self.units[i][j]] for j in range(c)] for i in range(r)])
            
        else:
            return self.eval()
        

    
      