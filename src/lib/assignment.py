from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .variable import ExperimentVariable
from .constraint import Different, Match, Constraint, Force, AllDifferent
from .participant import Participants
from .blocks import BlockFactor

class Assignment:
    """The assignment class matches each unit to an order of conditions.

    units: a list of unit objects 
    conditions_per_unit: how many experimental conditions does each unit witness/experience
    possible_orders: an object that maintains information about the possible 
        orderings of experimental condiitons, and the user-defined constraints
        on which conditions must/can appear in different positions in the order
    """
    def __init__(self):
        self.unit_variables = []
        self.constraints = []
        self.variables = []
        self.solver = z3.Solver()
        self.z3_vectors = []
        self.block_constraints = []
        self.dims = []

        self.z3_conditions = []

    def assign_conditions(self, subjects, variables=[], blocks = []):
        pass

    def assign_to_sequence(self, subjects, sequence, variables = []):

        assert isinstance(sequence, Sequence)

        self.dims = [subjects.n, sequence.n]
        self.unit_variables = [subjects, sequence]
        self.variables = variables

    def assign_to_blocks(self, blocks = [], variables = []):

        assert len(blocks) > 0

        for block in blocks:
            assert isinstance(block, BlockFactor)
            print(type(block))
            self.dims.append(block.n)
            self.unit_variables.append(block)

        self.variables = variables

    # ensure that we distinguish this
    def recieve_different_conditions(self, block):
        # I want this instead to return a constraint condition :)
        if isinstance(block, Participants):
            self.block_constraints.append(AllDifferent(block))
        

    def constrain_z3_values(self):
        # for all of the z3 variables relating to a specific variable, 
        # ensure that it can only be one of the values of the variable
        for variable in self.variables:
            for index in range(self.__num_z3_vars):
                self.solver.add(
                        And(
                            1 <= self.z3_vectors[variable][index], 
                            variable.n >= self.z3_vectors[variable][index]
                        ) 
                )
  
    def create_z3_for_conditions(self):
        # same for all any variables
        self.z3_conditions = [Int(f"C_{index + 1}") for index in range(self.__num_z3_vars)]
    
    # NOTE: using to same for z3 variables
    # I think I want to do this in assignment. (ie. assign conditions to sequence)
    def construct_z3_variable(self):
        z3_vectors = {}
        for variable in self.variables:
            z3_vectors[variable] = [Int(f"{str(variable)}_{index + 1}") for index in range(self.__num_z3_vars)]

        self.z3_vectors = z3_vectors


    
    # equvilant to above
    # conditions are a combination of variable assignments
    def constrain_z3_conditions(self):
        for i in range(self.__num_z3_vars):
            count = len(self.z3_vectors)-1
            test = []
            for var in self.z3_vectors:
                exp = self.z3_vectors[var][i] * 10**count
                test.append(exp)
                count -= 1

            exp = add(test, None, len(test))

            self.solver.add(self.z3_conditions[i] == exp)


    def get_all_models(self, combined_conditions):
        count = 0
        all_orders = []
        while self.solver.check() == sat:
            model = self.solver.model()

            block = []
            order = []
            for var in combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            # move this pls, to this class, not seq
            all_orders.append(order)
      
            # if this is And, we get a latin square
            test = Or(block)
            for constraint in self.constraints:
                if isinstance(constraint, AllDifferent):
                    test = And(block)
                    break

            self.solver.add(test)
            count += 1

        return all_orders

    def get_one_model(self, combined_conditions):
        if (self.solver.check() == sat):
            model = self.solver.model()
            return np.array([[model[combined_conditions[i]]] for i in range(len(combined_conditions))]).reshape(self.shape).tolist()

    # NOTE: won't generalize
    # probably should just be a class
    # ok cool, now it does. Probably should clean this up
    # functions like these are nice because the flattening does not matter
    def encoding_to_name(self, all_orders):
  
        orders = []
        test = np.array(all_orders).flatten().tolist()
        r = len(all_orders)
        c = len(all_orders[0])
        num_vars = len(self.variables)
        for i in range(len(test)):
            order = []
            # efficiently get first elem?
            var = ""
            for v in range(num_vars):
                x = int(str(test[i])[v])-1
                var+=str(self.variables[v].conditions[x])
                if v < len(self.variables)-1:
                    var+="-"
            order.append(var)
           
            orders.append(order)

        return np.array(orders).reshape(self.shape).tolist()
    
    # NOTE: won't generalize
    def eval_constraint(self, constraint, dim = 0):

        assert isinstance(constraint, Constraint)
        
        # this is perhaps a little wonky...
        # not sure if the loop unrolling should happen in 
        # the constraint class...
        test = {}
        for var in self.z3_vectors:
            if dim != 1:
                test[var] = np.array(self.z3_vectors[var]).reshape(self.shape).tolist()
            else: 
                test[var] = np.array(self.z3_vectors[var]).reshape(self.shape).transpose().tolist()
            print(test[var])
    



        if isinstance(constraint, Different) or isinstance(constraint, Match) or isinstance(constraint, Force):
            self.solver.add(constraint.eval_constraint(test))
        if isinstance(constraint, AllDifferent):
            self.constraints.append(constraint)

    # NOTE: won't generalize
    def determine_shape(self):
        # first, we want to get the shape of the array
        if len(self.block_constraints) > 0:
            shape = tuple(dim for dim in self.dims)
        else:
            # 1 dim array
            shape = (1, self.dims[1])

        # to referent shape later on
        self.shape = shape
        self.__num_z3_vars = np.prod(shape)


    # move out of this class
    def shape_array(self, arr):
        return np.array(arr).reshape(self.shape).tolist()

    # somehow merge eval and generate
    def eval(self):

        self.determine_shape()
        # result is just a flattened array with every variable
        # that we need. Number of variables is determined based on shape
        self.construct_z3_variable()

        dim = 0
        for unit_var in self.unit_variables:
            dim += 1
            for constraint in unit_var.constraints:
                self.eval_constraint(constraint, dim)


        self.constrain_z3_values()
        self.create_z3_for_conditions()

        combined_conditions_arr = self.shape_array(self.z3_conditions)

        dims = np.array(combined_conditions_arr).shape

          # # generalize these pls!!!!
        # # distinguish rows
        # for i in range(len(combined_conditions_arr)):
        #     print("in row constraints")
        #     print(np.array(combined_conditions_arr)[i, :])
        #     print(i)
        #     self.solver.add([Distinct(np.array(combined_conditions_arr)[i, :].tolist())])

        # # distinguish columns
        # if len(self.block_constraints) > 0:
        #     for i in range(len(combined_conditions_arr[0])):
        #         print("in column constraints")
        #         self.solver.add([Distinct(np.array(combined_conditions_arr)[:, i].tolist())])
        
        # starting to generalize the conditions
        # this generalizes the below code
        print(dims)

        # omg I think this solves this 0_o
        # super messy so pls fix this later
        for x in range(len(dims)):

            if x == 0 or len(self.block_constraints) > 0:
                keys = list(product(*[set(range(dims[i])) for i in range(len(dims)) if i != len(dims) - 1 - x]))
                print(keys)
                for tup in keys:
                    indexing = []
                    count = 0
                    for index in range(len(self.unit_variables)):
                        if index == x:
                            indexing.append(slice(None))
                        else:
                            indexing.append(tup[count])
                            count += 1

                    indexing.reverse()
                    self.solver.add([Distinct(np.array(combined_conditions_arr)[*indexing].tolist())])

            # print(f"{x+1}th dim")
            # if x == 0 or len(self.block_constraints) > 0:
            #     for i in range(dims[x]):
            #         print(i)
            #         indexing = []
            #         for index in range(len(self.unit_variables)):
            #             if index == x:
            #                 indexing.append(slice(None))
            #             else:
            #                 indexing.append(i)

            #         indexing.reverse()
            #         print(indexing)
            #         self.solver.add([Distinct(np.array(combined_conditions_arr)[*indexing].tolist())])

        
        self.constrain_z3_conditions()

        if len(self.block_constraints) > 0:
            test = self.get_one_model(self.z3_conditions)
        else: 
            test = self.get_all_models(self.z3_conditions)

        print(self.solver)
        print(test)
        
        return np.array(self.encoding_to_name(test))

        

    
      