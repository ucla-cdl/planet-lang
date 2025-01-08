from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .blocks import BlockFactor
from .candl import *
from .solver import AssignmentSolver, BitVecSolver
from .unit import Groups
from functools import reduce
from .members import Members

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

    def is_a_sequence(self, unit_variables):
        sequence = unit_variables[len(unit_variables)-1]
        return isinstance(sequence, Sequence) and len(sequence) > 1


    # NOTE: this is with a bitvec representation...
    # ensure that this works
    def eval(self):
        # perhaps this is where we create a different class?
        # we have so many new instance vars
        # these should maybe be classes or something? 
        self.shape = self.determine_shape()
        solver = BitVecSolver(self.shape, self.variables)

        dim = 0
        for unit_var in self.unit_variables:
            print(unit_var)
            for constraint in unit_var.constraints:
                # self.eval_constraint(constraint, dim)
                solver.eval_constraint(constraint, dim)
            dim += 1


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


        # FIXME: prettify/solidify this please 
        if self.is_a_sequence(self.unit_variables):
            print("here")
            block = BlockFactor(name = "sequence", levels=[f"{i}" for i in range(len(model))])
            self.groups.add_attribute(block)

        else:
            for variable in self.variables:
                block = BlockFactor(name = str(variable), levels=[str(cond) for cond in variable.conditions])
                self.groups.add_attribute(block)
       
        return np.array(solver.encoding_to_name(model, self.variables))

    def get_groups(self):
        assert self.groups != None
        return self.groups
    
    
    def get_unit_vars(self):
        return self.unit_variables



class GroupAssignment(Assignment):
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

    """
    def __init__(self, participants, num_groups_participant_in = 1, groups=None):
        Assignment.__init__(self)

        self.participants = participants
        self.num_groups_participants_in = num_groups_participant_in
        self.groups = groups

        num_participants = len(participants) * num_groups_participant_in
        num_groups = len(groups)
        blocks = groups.get_attributes()

        self.blocks = blocks


        participant_per_group = int(num_participants / num_groups)
        shape = [len(blocks[i]) for i in range(len(blocks))]

        block_dims = 1
        for block in blocks:
            block_dims *= len(block)

        shape.extend([int(num_groups/block_dims), participant_per_group])
        shape = tuple(shape)

        self.shape = shape
        print(shape)

        assert num_groups_participant_in * len(participants) >= reduce(lambda x, y: x * y, shape)

        num_units_per_group = shape[len(shape)-1]
        self.members = Members(num_units_per_group)

        self.variables = [participants]
        self.variables.extend([attr for attr in participants.attributes])
        self.solver = AssignmentSolver(shape, self.variables, blocks)

        """
        observe: these are all constraints on group members (when dim is len(shape) - 1)
            the constraints involving other dims are wrt. that dim, but place constraints
            on the participants
        """
        participants.occurs_n_times(num_groups_participant_in)

        if len(participants.attributes) > 0:
            self.solver.nested_assignment() # axiom

        self.members.all_different() # this is actually group_members.all_different()


    def eval(self):

        for constraint in self.participants.constraints:
            self.solver.eval_constraint(constraint, len(self.shape) - 1)

        for constraint in self.members.constraints:
            self.solver.eval_constraint(constraint, len(self.shape) - 1)

        for constraint in self.blocks[0].constraints:
            self.solver.eval_constraint(constraint, 0)


        model = self.solver.get_one_model()
        assert len(model) > 0
        model = np.array(model).reshape(self.shape).tolist()
        
        mapping = np.array(self.solver.encoding_to_name(model, self.variables))
        return mapping



