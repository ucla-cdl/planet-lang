from z3 import *
from .constraint import Constraint, Different, Match, Force, AllDifferent
import numpy as np
from .candl import *
from .helpers import *
from .translate import Translate

class Solver:
    def __init__(self, shape, variables):
        self.shape = shape
        self.variables = variables
        self.__num_z3_vars = np.prod(self.shape)
        self.solver = z3.Solver()
        self.translate = Translate()

        self.construct_z3_variable()
        self.constrain_z3_values()
        self.create_z3_for_conditions()
        self.constrain_z3_conditions()

    # you can come up with a better name
    def constrain_z3_values(self):
        # for all of the z3 variables relating to a specific variable, 
        # ensure that it can only be assigned to one of the levels
        # of the specific variable
        for variable in self.variables:
            # NOTE: z3 vectors is stored as a flattened array
            for index in range(self.__num_z3_vars):
                self.solver.add(
                        And(
                            1 <= self.z3_vectors[variable][index], 
                            variable.n >= self.z3_vectors[variable][index]
                        ) 
                )

    def z3_of_same_type(self, label, n):
        return [Int(f"{label}_{index + 1}") for index in range(n)]

    # FIXME: function that merges these
    # z3 variable for the overal condition assigned to a unit. 
    # for example, an n by n lating square has n*n z3 variables 
    # for each cell of the square. represented by the flattened array
    def create_z3_for_conditions(self):
        self.z3_conditions = self.z3_of_same_type("C", self.__num_z3_vars)
    
    # NOTE: using to same for z3 variables
    # I think I want to do this in assignment. (ie. assign conditions to sequence)

    # it appears that the above function is closely related to this one...
    def construct_z3_variable(self):
        z3_vectors = {}
        for variable in self.variables:
            z3_vectors[variable] = self.z3_of_same_type(str(variable), self.__num_z3_vars)
            
            [Int(f"{str(variable)}_{index + 1}") for index in range(self.__num_z3_vars)]
            
        self.z3_vectors = z3_vectors
    
    # conditions are a combination of variable assignments
    # constrain conditions based on variable constraints
    def constrain_z3_conditions(self):
        # flattened representation
        for i in range(self.__num_z3_vars):
            # start at the last index because the first variable
            # is the number closest to the left in the variable name
            place = len(self.z3_vectors)-1
            numbers = []
            for var in self.z3_vectors:
                num = self.z3_vectors[var][i] * 10**place
                numbers.append(num)
                place -= 1

            # this adds all of the numbers in the array
            # I could've used numpy... whoops
            combined_number = add(numbers, None, len(numbers))

            # constrain z3 variable s.t. it is the concatination
            # of the assigned values to it's respective variables
            self.solver.add(self.z3_conditions[i] == combined_number)

        # NOTE: won't generalize
    # FIXME: following compiler-style, maybe just translate all here
    def eval_constraint(self, constraint, dim = 0):

        assert isinstance(constraint, Constraint)
        # this is perhaps a little wonky...
        # not sure if the loop unrolling should happen in 
        # the constraint class...
        dim_indexings = create_indexing(dim, self.shape)
        
        # how can we utilize transpose?
        if isinstance(constraint, Different):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

            dim_variables = []
            for indexing in dim_indexings:
                dim_variables.append(np.array(self.z3_vectors[var]).reshape(self.shape)[*indexing].tolist())
    
            for row in dim_variables:
                left = row[i1]
                right = row[i2]
                __z3__ = self.translate.different(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Match):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

            dim_variables = []
            for indexing in dim_indexings:
                dim_variables.append(np.array(self.z3_vectors[var]).reshape(self.shape)[*indexing].tolist())
    
            for row in dim_variables:
                left = row[i1]
                right = row[i2]
                __z3__ = self.translate.match(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Force):
            var = constraint.get_variable()
            i = constraint.get_index()
            condition = constraint.get_condition()

            dim_variables = []
            for indexing in dim_indexings:
                dim_variables.append(np.array(self.z3_vectors[var]).reshape(self.shape)[*indexing].tolist())
    
            for row in dim_variables:
                left = row[i]
                __z3__ = self.translate.match(left, condition)
                self.solver.add(__z3__)

        if isinstance(constraint, AllDifferent):
            # could you prettify this?
            z3_with_shape = shape_array(self.z3_conditions, self.shape)
            for indexing in dim_indexings:
                arr_to_constrain = np.array(z3_with_shape)[*indexing].tolist()
                self.solver.add([Distinct(arr_to_constrain)])

        # works when z3 representation is a matrix 
    def get_one_model(self):
        all_assignments = []

        if (self.solver.check() == sat):
            model = self.solver.model()

            for var in self.z3_conditions:
                all_assignments.append(model.evaluate(model[var]))

        return all_assignments
    
    # works when z3 rep iterates through many arrays
    # NOTE: should I merge these two functions?
    def get_all_models(self):
 
        all_orders = []
        self.solver.push()

        while self.solver.check() == sat:
            model = self.solver.model()

            block = []
            order = []
            for var in self.z3_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            all_orders.append(order)
            self.solver.add(Or(block))

        self.solver.pop()
        return all_orders

    def solve(self):
        print(self.solver)