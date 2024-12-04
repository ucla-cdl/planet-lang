from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .blocks import BlockFactor
from .candl import *
from .solver import Solver, BitVecSolver
from .unit import Groups
from .variable import ExperimentVariable
from .constraint import Force

class Assignment:
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

    """
    def __init__(self):
        self.unit_variables = []
        self.variables = []
        self.diff = False

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
    
    def all_different(self):
        self.diff = True


    # NOTE: this is with a bitvec representation...
    # ensure that this works
    def eval(self):
        # perhaps this is where we create a different class?
        # we have so many new instance vars
        # these should maybe be classes or something? 
        self.shape = self.determine_shape()
        solver = BitVecSolver(self.shape, self.variables)

        dim = len(self.unit_variables) - 1
        for unit_var in self.unit_variables:
            for constraint in unit_var.constraints:
                # self.eval_constraint(constraint, dim)
                solver.eval_constraint(constraint, dim)
            dim -= 1

        if self.diff:
            solver.all_different()

        # FIXME: kind of ugly
        if len(self.unit_variables[0].constraints) > 0:
            model = solver.get_one_model()
            assert len(model) > 0
            model = np.array(model).reshape(self.shape).tolist()
        else: 
            model = solver.get_all_models()

        if len(self.unit_variables[0].constraints) > 0:
            assert self.unit_variables[0].n % len(model) == 0

        self.groups = Groups(len(model), model)
        return np.array(solver.encoding_to_name(model, self.variables))

    def get_groups(self):
        assert self.groups != None
        return self.groups
    
    def get_unit_vars(self):
        return self.unit_variables

    
    def assign_participants_to_groups(self, num_groups_participant_in = 1, groups=None, never_occur_together = False):
        participants = self.unit_variables[0]
        num_participants = len(participants) * num_groups_participant_in

        if groups is None:
            groups = self.groups

        num_groups = len(groups)

        assert num_groups % len(self.groups) == 0
      
        # NOTE: should be available option
        participant_per_group = int(num_participants / num_groups)

        shape = (num_groups, participant_per_group)
        # this is important and specific to GroupAssignment
        assert num_groups_participant_in * len(participants) >= shape[0] * shape[1]
    
        variables = [participants]
        variables.extend([attr for attr in participants.attributes])
        solver = BitVecSolver(shape, variables)


        # this is a specific constraint. Better way to expose?
        participants.occurs_n_times(num_groups_participant_in)
        constraint = participants.constraints[0]
        solver.eval_constraint(constraint, 0)

        # this is an axiom, and this is such a wonky way to do this
        participants.all_different()
        constraint = participants.constraints[1]
        solver.eval_constraint(constraint, 0)
        
        dim = 1
        for constraint in groups.constraints:
            solver.eval_constraint(constraint, dim)


        if never_occur_together:
            solver.never_occur_together()
        if len(participants.attributes) > 0:
            solver.nested_assignment() # axiom

        model = solver.get_one_model()
        assert len(model) > 0
        model = np.array(model).reshape(shape).tolist()
        print("\n participants mapping to groups")
        print(np.array(solver.encoding_to_name(model, variables)))


    # NOTE: should we be able to directly place constraints on this class?


    # somehow merge eval and generate
    # def eval(self):
    #     # perhaps this is where we create a different class?
    #     # we have so many new instance vars
    #     # these should maybe be classes or something? 
    #     self.shape = self.determine_shape()
    #     solver = Solver(self.shape, self.variables)

    #     dim = len(self.unit_variables) - 1
    #     for unit_var in self.unit_variables:
    #         for constraint in unit_var.constraints:
    #             # self.eval_constraint(constraint, dim)
    #             solver.eval_constraint(constraint, dim)
    #         dim -= 1

    #     if self.diff:
    #         solver.all_different()

    #     # FIXME: kind of ugly
    #     if len(self.unit_variables[0].constraints) > 0:
    #         model = solver.get_one_model()
    #         assert len(model) > 0

    #         model = np.array(model).reshape(self.shape).tolist()
    #     else: 
    #         model = solver.get_all_models()

    #     assert self.unit_variables[0].n % len(model) == 0
    #     # return a numpy representation of the assignment
    #     self.groups = Groups(len(model), model)
    #     return np.array(self.encoding_to_name(model, self.variables))



