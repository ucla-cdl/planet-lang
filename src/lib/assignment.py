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
    units.eval()
    num_plans = len(plans)
    
    duckdb.sql(f"update participants set plan = floor(random() * {num_plans}) + 1")
    # duckdb.sql("select * from participants order by random() limit 3").show()
    duckdb.sql(f"select * from {units.table}").show()
    # duckdb.sql("SELECT test.pid, plan FROM (SELECT row_number() OVER (ORDER BY random()) as id, pid FROM participants ORDER BY RANDOM()) test join participants secondary on secondary.pid = test.pid").show()

    duckdb.sql(f"select count(*) from {units.table} group by plan").show()


class Assignment:
    """The assignment class matches every unit to an order of conditions
        based on constraints set on unit variables, such as block factors
        of participants, pid, and the state of observation of a subject. 

    """
    def __init__(self, subjects, sequence, variables = []):
        self.variables = []
        self.seq = None
        self.units = None
        self.num_trials = 0
        self.solver = None
        self.solver_test = None
        self.assign(subjects, sequence, variables)

    def assign(self, subjects, sequence, variables = []):
        assert isinstance(sequence, Sequence)
        assert isinstance(subjects, Units) or subjects is None


        self.units = subjects
        self.seq = sequence
        self.num_trials = len(sequence)
        self.variables = variables
        


        if len(subjects):
            self.shape = self.determine_shape()
            self.solver = BitVecSolver(self.shape, self.variables)
        else:
            self.solver = BitVecSolver(tuple([1, self.num_trials]), self.variables)

  
        # return back in original form
    
    def determine_shape(self, limit = False):
        if limit: 
            n = 1
        else: 
            n = len(self.units)

        return tuple([n, self.num_trials])
    
    # FIXME: creating block matrix for specific test case 
    # Note: use for creating blocks

    # NEED TO DECOUPLE THIS
    def match_inner(self, v, w, h):

        if len(self.units):
            
            n = int(self.shape[0] / h)
            m = int(self.shape[1] / w)


            for i in range(n):
                for j in range(m):
                    
                    self.solver.match_block(v, [(i*h + 0, i * h  + h, 1), (j*w + 0, j * w + w, 1)])

    def match_outer(self, v, w, h):

        # NEEDS TO BE it's own func / constraint option. Don't treat these together 
        for i in range(h):
            for j in range(w):
            
                self.solver.match_block(v, [(i, self.shape[0], h), (j, self.shape[1], w)])


    def counterbalance(self, v, w, h, stride = [1, 1]):
        block = [(0, h, stride[0]), (0, w, stride[1])]

        self.solver.counterbalance(block, v)

    def start_with(self, variable, condition):
        print("start")
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
  