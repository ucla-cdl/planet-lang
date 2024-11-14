from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .variable import ExperimentVariable
from .constraint import Different, Match, Constraint, Force, AllDifferent
from .participant import Participants
from .blocks import BlockFactor
from .candl import *

class Assignment:
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

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


    # I think I want these to create a solver class
    def assign_to_sequence(self, subjects, sequence, variables = []):
        assert isinstance(sequence, Sequence)
        # assigning to sequence is a special case of blocking
        self.assign_to_blocks(blocks = [subjects, sequence], variables = variables)

    def assign_to_blocks(self, blocks = [], variables = []):

        assert len(blocks) > 0

        for block in blocks:
            assert isinstance(block, BlockFactor)
            # get the number of block factor levels for every block
            self.dims.append(block.n)
            # we consider a block factor a unit variable
            self.unit_variables.append(block)

        self.variables = variables

    # ensure that we distinguish this
    def recieve_different_conditions(self, block):
        # change this... constraint should probably be in participant/block class
        if isinstance(block, Participants):
            self.block_constraints.append(AllDifferent(block))
        
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


    # FIXME: function that merges these
    # z3 variable for the overal condition assigned to a unit. 
    # for example, an n by n lating square has n*n z3 variables 
    # for each cell of the square. represented by the flattened array
    def create_z3_for_conditions(self):
        self.z3_conditions = [Int(f"C_{index + 1}") for index in range(self.__num_z3_vars)]
    
    # NOTE: using to same for z3 variables
    # I think I want to do this in assignment. (ie. assign conditions to sequence)

    # it appears that the above function is closely related to this one...
    def construct_z3_variable(self):
        z3_vectors = {}
        for variable in self.variables:
            z3_vectors[variable] = [Int(f"{str(variable)}_{index + 1}") for index in range(self.__num_z3_vars)]
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


    # works when z3 rep iterates through many arrays
    # NOTE: should I merge these two functions?
    def get_all_models(self, combined_conditions):
 
        all_orders = []
        self.solver.push()

        while self.solver.check() == sat:
            model = self.solver.model()

            block = []
            order = []
            for var in combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            all_orders.append(order)
            self.solver.add(Or(block))

        self.solver.pop()
        return all_orders

    # works when z3 representation is a matrix 
    def get_one_model(self, combined_conditions):
        all_assignments = []

        if (self.solver.check() == sat):
            model = self.solver.model()

            for var in combined_conditions:
                all_assignments.append(model.evaluate(model[var]))

        orders = np.array(all_assignments).reshape(self.shape).tolist()
        return orders

    # NOTE: should this be it's own class? hmmm
    #   - like some type of encode/decode class?
    # functions like these are nice because the flattening does not effect eval
    # should this be in variable and condition classes?
    def encoding_to_name(self, all_orders):
  
        # this makes life much easier
        z3_assignments = flatten_array(all_orders)
        num_vars = len(self.variables)
        
        orders = []
        for z3_var in z3_assignments:
            assignment = str(z3_var)

            order = []
            decoded_assignment = ""
            # there is probably a more efficient way to do this
            for i in range(num_vars):
                # get the ith variable's assignment
                variable_assignment = int(assignment[i])-1
                condition = self.variables[i].conditions[variable_assignment]
                decoded_assignment+=str(condition)

                if i < len(self.variables)-1:
                    decoded_assignment+="-"

            order.append(decoded_assignment)
            orders.append(order)

        # return back in original form
        return shape_array(orders, np.array(all_orders).shape)
    
    # NOTE: won't generalize
    # FIXME: following compiler-style, maybe just translate all here
    def eval_constraint(self, constraint, dim = 0):

        assert isinstance(constraint, Constraint)
        
        # this is perhaps a little wonky...
        # not sure if the loop unrolling should happen in 
        # the constraint class...
        test = {}
     
        
        dim_indexings = create_indexing(dim, self.shape)
        # how can we utilize transpose?
        for var in self.z3_vectors:
            for indexing in dim_indexings:
                if var not in test:
                    test[var] = []
                test[var].append(np.array(self.z3_vectors[var]).reshape(self.shape)[*indexing].tolist())

    
        if isinstance(constraint, Different) or isinstance(constraint, Match) or isinstance(constraint, Force):
            self.solver.add(constraint.eval_constraint(test))
        if isinstance(constraint, AllDifferent):
            self.constraints.append(constraint)

    # NOTE: won't generalize
    def determine_shape(self):
        # first, we want to get the shape of the array
        dim_0_constraints = self.unit_variables[0].constraints
        print(dim_0_constraints)
        if len(dim_0_constraints) > 0:
            shape = tuple(dim for dim in self.dims)
        else:
            # the participants don't have any constraints (or row block)
            # all dims except for the first 
            other_dims = [self.dims[i] for i in range(len(self.dims)) if i != 0]
            shape = (1, *other_dims)

        # to referent shape later on
        self.shape = shape
        self.__num_z3_vars = np.prod(shape)

    # somehow merge eval and generate
    def eval(self):

        # perhaps this is where we create a different class?
        # we have so many new instance vars
        self.determine_shape()
        self.construct_z3_variable()
        self.constrain_z3_values()
        self.create_z3_for_conditions()
        self.constrain_z3_conditions()


        # FIXME: combine the two loop lines in constraint eval 

        # NOTE: quick fix, come back to this
        dim = len(self.unit_variables) - 1
        for unit_var in self.unit_variables:
            print(unit_var)
            for constraint in unit_var.constraints:
                self.eval_constraint(constraint, dim)

            dim -= 1


        # next steps: check for dim constraints of both type
        # apply constraints in the same way :) 
        self.z3_conditions_with_shape = shape_array(self.z3_conditions, self.shape)
        # for every dimension
        for dim in range(len(self.shape)):
            # only apply this if the other dimensions have this constraint
            if dim == 0 or len(self.unit_variables[0].constraints) > 0:
                # create the indexings to get all arrays of vals at specific dim
                dim_indexings = create_indexing(dim, self.shape)
                # for every way of indexing (ie. all levels of all other dims)
                # add constraint that the vals in this dim are distinct at 
                # every level of every other dimension
                for indexing in dim_indexings:
                    arr_to_constrain = np.array(self.z3_conditions_with_shape)[*indexing].tolist()
                    self.solver.add([Distinct(arr_to_constrain)])

        # FIXME
        if len(self.unit_variables[0].constraints) > 0:
            test = self.get_one_model(self.z3_conditions)
        else: 
            test = self.get_all_models(self.z3_conditions)


        # return a numpy representation of the assignment
        return np.array(self.encoding_to_name(test))

        

    
      