from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .blocks import BlockFactor
from .candl import *
from .solver import  BitVecSolver
from .unit import Groups

import math

class Assignment:
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

    """
    def __init__(self):
        self.unit_variables = []
        self.variables = []

        self.units = None
        self.num_trials = 0

        self.flag = False

    # I think I want these to create a solver class
    def assign(self, subjects, sequence, variables = []):
        assert isinstance(sequence, Sequence)
        # assigning to sequence is a special case of blocking
        self.units = subjects
        self.num_trials = len(sequence)
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
    def encoding_to_name(self, all_orders, variables):
  
        # this makes life much easier
        z3_assignments = flatten_array(all_orders)
        num_vars = len(variables)
        
        orders = []
        for z3_var in z3_assignments:
            assignment = str(z3_var)

            order = []
            decoded_assignment = ""
            # there is probably a more efficient way to do this
            for i in range(num_vars):
                # get the ith variable's assignment
                variable_assignment = int(assignment[i])-1
                condition = variables[i].conditions[variable_assignment]
                decoded_assignment+=str(condition)

                if i < len(variables)-1:
                    decoded_assignment+="-"

            order.append(decoded_assignment)
            orders.append(order)

        # return back in original form
        return shape_array(orders, np.array(all_orders).shape)
    

        # return back in original form
    
    def determine_shape(self):
        shape = tuple([len(self.units), self.num_trials])
        return shape
    
    def test(self):
        self.flag = True
    

    # NOTE: this is with a bitvec representation...
    # ensure that this works
    def eval(self):
        # perhaps this is where we create a different class?
        # we have so many new instance vars
        # these should maybe be classes or something? 
        self.shape = self.determine_shape()
        solver = BitVecSolver(self.shape, self.variables)
        solver.counterbalance()

        n = int(self.shape[0] / 3)
        m = int(self.shape[1] / 3)

        if self.flag:
            for i in range(n):
                for j in range(m):
                    solver.match_block([(i*3 + 0, i * 3  + 3), (j*3 + 0, j * 3 + 3)])

        dim = 0
        for unit_var in self.unit_variables:
            for constraint in unit_var.constraints:
                # self.eval_constraint(constraint, dim)
                solver.eval_constraint(constraint, dim)
            dim += 1



        model = solver.get_one_model()
        assert len(model) > 0
        model = np.array(model).reshape(self.shape).tolist()
     
        if len(self.unit_variables[0].constraints) > 0:
            assert self.unit_variables[0].n % len(model) == 0

        return np.array(solver.encoding_to_name(model, self.variables))

    def get_groups(self):
        assert self.groups != None
        return self.groups
    
    
    def get_unit_vars(self):
        return self.unit_variables

