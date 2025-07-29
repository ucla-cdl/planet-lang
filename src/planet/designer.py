# External libraries
from z3 import *                # Requires: pip install z3-solver
import numpy as np

# Core system modules (planet package)
from planet.orders import Sequence
from planet.candl import *          #
from planet.helpers import *       
from planet.narray import *
from planet.solver import BitVecSolver
from planet.constraint import (
    StartWith, Counterbalance, NoRepeat,
    InnerBlock, OuterBlock, Constraint,
    SetRank, SetPosition, AbsoluteRank
)
from planet.variable import MultiFactVariable
from planet.unit import Units

# NOTE: combine this with des pls
class Designer:
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

    """
    def __init__(self):
        self.constraints = []

    def start(self, subjects, sequence, variables=[]):
        assert isinstance(sequence, Sequence)
        print(subjects)
        assert isinstance(subjects, Units)
        assert len(variables) > 0

        self.units = subjects
        self.seq = sequence
        self.num_trials = len(sequence)
        self.variables = variables
        self.shape = self.determine_shape()
        self.solver = BitVecSolver(self.shape, self.variables)

    def _get_experiment_variables(self, constraint):
        if isinstance(constraint.variable, MultiFactVariable):
            return constraint.get_variable().get_variables()
        else:    
            return [constraint.get_variable()]

    def eval_constraints(self, constraints, groups, width):
        # Process constraints
        for constraint in constraints:
            assert isinstance(constraint, Constraint)
            variable = self._get_experiment_variables(constraint)

            match constraint:
                
                case Counterbalance():
                    # FIXME
                    if groups:
                        constraint.width = (
                            constraint.width if constraint.width else width
                        )
                        constraint.height = (
                            constraint.height if constraint.height else len(groups)
                        )

                    self.counterbalance(
                        variable,
                        w=constraint.width,
                        h=constraint.height,
                        stride=constraint.stride,
                    )

                case NoRepeat():
            
                        self.solver.all_different(
                            variable, 
                            constraint.width, 
                            constraint.stride
                        )

                case StartWith():
                    self.start_with(
                        constraint.variable, 
                        constraint.condition
                    )
                
                case SetPosition():
                    self.set_position(
                        constraint.variable, 
                        constraint.condition,
                        constraint.position
                    )

                case SetRank():
                    self.set_rank(
                        constraint.variable, 
                        constraint.condition,
                        constraint.rank,
                        constraint.condition2
                    )

                case AbsoluteRank():
                    self.absolute_rank(
                        constraint.variable, 
                        constraint.ranks
                    )

                case InnerBlock():
                    self.match_inner(
                        constraint.variable, 
                        constraint.width, 
                        constraint.height
                    )

                case OuterBlock():
                    print(constraint.variable, constraint.width, constraint.height, constraint.stride)
                    self.match_outer(
                        constraint.variable, 
                        constraint.width, 
                        constraint.height
                    )
                case _:
                    raise ValueError("Could not identify proper constraint")
        
    def determine_shape(self):
        if len(self.units): 
            n = len(self.units)
        else: 
            n = 1

        return tuple([n, self.num_trials])
    
    # FIXME: creating block matrix for specific test case 
    # Note: use for creating blocks

    # NEED TO DECOUPLE THIS
    def match_inner(self, variable, width, height):
        print("inner")
        # get number of block matrices per column
        n = int(self.shape[0] / height)
        # get number of block matrices per row
        m = int(self.shape[1] / width)
       
        for i in range(n):
            for j in range(m):
                self.solver.match_block(
                    variable, 
                    [
                        (i*height + 0, i * height  + height, 1)
                        , (j*width + 0, j * width + width, 1)
                    ]
                )

        



    def match_outer(self, v, w, h):
        print("outer", v, w, h)
        # NEEDS TO BE it's own func / constraint option. Don't treat these together 
        for i in range(h):
            for j in range(w):
                
                self.solver.match_block(v, [(i, self.shape[0], h), (j, self.shape[1], w)])

    def counterbalance(self, v, w, h, stride = [1, 1]):
        block = [(0, h, stride[0]), (0, w, stride[1])]
        self.solver.counterbalance(block, v)

    def start_with(self, variable, condition):
        self.solver.start_with(variable, variable.conditions.index(condition))

    def set_rank(self, variable, condition, rank, condition2):
        self.solver.set_rank(variable, variable.conditions.index(condition), rank, variable.conditions.index(condition2))
    
    def set_position(self, variable, condition, pos):
        self.solver.set_position(variable, variable.conditions.index(condition), pos)
    
    def absolute_rank(self, variable, ranks):
        transformed_ranks = {variable.conditions.index(condition): rank for condition, rank in ranks.items()}
        self.solver.absolute_rank(variable, transformed_ranks)
    

    def get_groups(self, model):
        if not len(self.units):
            self.units.n = len(model)



    # NOTE: this is with a bitvec representation...
    # ensure that this works
    def eval(self):
        # perhaps this is where we create a different class?
        # we have so many new instance vars
        # these should maybe be classes or something? 
        if len(self.units):
            model = self.solver.get_one_model()
            assert len(model) > 0
            model = np.array(model).reshape(self.shape).tolist()
            return np.array(self.solver.encoding_to_name(model, self.variables))
        else:
            model = self.solver.get_all_models()
            self.get_groups(model)
            return np.array(self.solver.encoding_to_name(model, self.variables))
            
  
    # NOTE: this is with a bitvec representation...
    # ensure that this works
    def eval_all(self):
        # perhaps this is where we create a different class?
        # we have so many new instance vars
        # these should maybe be classes or something? 
        if len(self.units):
            models = self.solver.get_all_models()

            ret = []
            for model in models:
                assert len(model) > 0
                model = np.array(model).reshape(self.shape).tolist()
                ret.append(np.array(self.solver.encoding_to_name(model, self.variables)))

            return ret
        else:
            model = self.solver.get_all_models()
            self.get_groups(model)
            return np.array(self.solver.encoding_to_name(model, self.variables))
            
