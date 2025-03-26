from z3 import *
from lib.orders import Sequence
from lib.candl import *
from .helpers import *
from .narray import *
import numpy as np
from .candl import *
from .solver import  BitVecSolver
from lib.constraint import StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock, Constraint
from lib.unit import Groups, Units

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
        assert isinstance(subjects, Units)
        assert len(variables) > 0

        self.units = subjects
        self.seq = sequence
        self.num_trials = len(sequence)
        self.variables = variables
        self.shape = self.determine_shape()
        self.solver = BitVecSolver(self.shape, self.variables)


    def eval_constraints(self, constraints, groups, width):
        # Process constraints
        for constraint in constraints:
            assert isinstance(constraint, Constraint)
            match constraint:
                
                case Counterbalance():
                    if groups:
                        constraint.width = (
                            constraint.width if constraint.width else width
                        )
                        constraint.height = (
                            constraint.height if constraint.height else len(groups)
                        )
                    self.counterbalance(
                        constraint.variable,
                        w=constraint.width,
                        h=constraint.height,
                        stride=constraint.stride,
                    )

                case NoRepeat():
                    self.solver.all_different(
                        constraint.variable, 
                        constraint.width, 
                        constraint.stride
                    )

                case StartWith():
                    self.start_with(
                        constraint.variable, 
                        constraint.condition
                    )

                case InnerBlock():
                    self.match_inner(
                        constraint.variable, 
                        constraint.width, 
                        constraint.height
                    )

                case OuterBlock():
                    self.match_outer(
                        constraint.variable, 
                        constraint.width, 
                        constraint.height
                    )
                case _:
                    print("failure")
        



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
        # NEEDS TO BE it's own func / constraint option. Don't treat these together 
        for i in range(h):
            for j in range(w):
                
                self.solver.match_block(v, [(i, self.shape[0], h), (j, self.shape[1], w)])

    def counterbalance(self, v, w, h, stride = [1, 1]):
        block = [(0, h, stride[0]), (0, w, stride[1])]
        self.solver.counterbalance(block, v)

    def start_with(self, variable, condition):
        self.solver.start_with(variable, variable.conditions.index(condition))
    
    

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
            
