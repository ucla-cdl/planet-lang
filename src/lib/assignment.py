from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .constraint import Different, Match, Constraint, Force, AllDifferent
from .participant import Participants
from .blocks import BlockFactor
from .candl import *
from .translate import Translate
from .solver import Solver

class Assignment:
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

    """
    def __init__(self):
        self.unit_variables = []
        self.variables = []

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

        self.unit_variables = blocks
        self.variables = variables

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
    

    def determine_shape(self):
        # first, we want to get the shape of the array
        # we consider a block factor a unit variable
        dim_0_constraints = self.unit_variables[0].constraints
        dims = [len(var) for var in self.unit_variables]
        if len(dim_0_constraints) > 0:
            shape = tuple(dim for dim in dims)
        else:
            # the participants don't have any constraints (or row block)
            # all dims except for the first 
            other_dims = [dims[i] for i in range(len(dims)) if i != 0]
            shape = (1, *other_dims)

        return shape

    # somehow merge eval and generate
    def eval(self):
        # perhaps this is where we create a different class?
        # we have so many new instance vars
        # these should maybe be classes or something? 
        self.shape = self.determine_shape()
        solver = Solver(self.shape, self.variables)

        dim = len(self.unit_variables) - 1
        for unit_var in self.unit_variables:
            for constraint in unit_var.constraints:
                # self.eval_constraint(constraint, dim)
                solver.eval_constraint(constraint, dim)
            dim -= 1

        # FIXME: kind of ugly
        if len(self.unit_variables[0].constraints) > 0:
            model = solver.get_one_model()
            model = np.array(model).reshape(self.shape).tolist()
        else: 
            model = solver.get_all_models()

        # return a numpy representation of the assignment
        return np.array(self.encoding_to_name(model))

        

    
      