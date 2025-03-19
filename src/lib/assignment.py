from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .candl import *
from .solver import  BitVecSolver
from .unit import Units, Groups

import duckdb

def assign_counterbalance(units, plans):
    units.eval()

    
    if plans.counterbalanced:
        plans = plans.eval()

    else:
        plans = plans.random(units)
    
    num_plans = len(plans)
    num_participants = units.n
    duckdb.sql("CREATE TABLE members (plan int)")

    
    num_per_group = int(num_participants / num_plans)
    
    for i in range(1, num_plans+1):
        for _ in range(1, num_per_group+1):
            duckdb.sql(f"insert into members values ({i})")

    duckdb.sql(""" select participants.pid, members.plan from 
                                (select      *, 
                                            row_number() over(order by uuid()) rand
                                from        members) members, participants
               where participants.pid = members.rand
                        
           """).show()
    
    
    

    duckdb.sql(""" select count(*) from (select participants.pid, members.plan from 
                                (select      *, 
                                            row_number() over(order by uuid()) rand
                                from        members) members, participants
               where participants.pid = members.rand) group by plan
                        
           """).show()
    
def assign(units, plans):
    return assign_counterbalance(units, plans)


class Assignment:
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

    """
    def __init__(self, subjects, sequence, variables = []):
        assert isinstance(sequence, Sequence)
        assert isinstance(subjects, Units)
        assert len(variables) > 0

        self.units = subjects
        self.seq = sequence
        self.num_trials = len(sequence)
        self.variables = variables
        self.shape = self.determine_shape()
        self.solver = BitVecSolver(self.shape, self.variables)

    
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
            self.units.n = len(model)
            print(np.array(self.solver.encoding_to_name(model, self.variables)))
            return np.array(self.solver.encoding_to_name(model, self.variables))
  