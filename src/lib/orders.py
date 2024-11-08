from .condition import ConditionTest
from .helpers import DEBUG, add
from z3 import *
import numpy as np
from .variable import ExperimentVariable
from .constraint import Different, Match, Constraint, Force

class Sequence:
    """The PossibleOrders class represents all of the possible
        orders of conditions in an experiment, where each order
        is an experimental group

    n: the number of conditions in each order
    we use argv so the user can pass any number of variables
    because experiments have varying amount of variables
    """
    def __init__(self, n, *argv):
        self.sequence_length = n 
        self.solver = z3.Solver()

        self.variables = self.parse_args(argv) # ExperimentVariables
        self.num_variables = len(self.variables) # num indep vars in experiment
        self.constraints = []


        self.z3_vectors = None # rep each var in z3


        self.all_orders = [] # stores all possible orders given constraint
        self.n = n



    # I think I want to do this in assignment. (ie. assign conditions to sequence)
    def construct_z3_variable(self, variables):
        z3_vectors = {}
        for variable in variables:
            z3_vectors[variable] = [Int(f"{str(variable)}_{index + 1}") for index in range(self.sequence_length)]
        self.z3_vectors = z3_vectors

    def parse_args(self, variables):
        ret = []
        for var in variables:
            assert isinstance(var, ExperimentVariable)
            ret.append(var)
        return ret
    
    def eval_constraint(self, constraint):

        assert isinstance(constraint, Constraint)

        if isinstance(constraint, Different) or isinstance(constraint, Match):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

        if isinstance(constraint, Different):
            self.solver.add(self.z3_vectors[var][i1] != self.z3_vectors[var][i2])
        if isinstance(constraint, Match):
            self.solver.add(self.z3_vectors[var][i1] == self.z3_vectors[var][i2])
        if isinstance(constraint, Force):
            variable = constraint.get_variable()
            val = constraint.get_condition()
            i = constraint.get_index()
            self.solver.add(self.z3_vectors[variable][i] == val)

    def different(self, i1, i2, variable):
        constraint = Different(i1, i2, variable)
        self.constraints.append(constraint)

    def match(self, i1, i2, variable):
        constraint = Match(i1, i2, variable)
        self.constraints.append(constraint)


    # not finished (need a mapping of indices to variable assignments)
    def force(self, i, variable, condition):
        val = 0

        # probably somethign more efficient... do we want to store 
        # these mappings, so we dont have to comput every time and then loop?
        # reasoning not to is that no variable should have many conditions
        condition_names = list(map(lambda condition: condition.name, variable.conditions))
   
        val = condition_names.index(condition) + 1
        constraint = Force(variable, val, i)
        self.constraints.append(constraint)
        
    # should this just be a class? probabably...
    def encoding_to_name(self):
        orders = []
        for i in range(len(self.all_orders)):
            order = []
            for j in range(len(self.all_orders[0])):
                # efficiently get first elem?
                var = ""
                for v in range(len(self.variables)):

                    x = int(str(self.all_orders[i][j])[v])-1
                    var+=str(self.variables[v].conditions[x])
                    if v < len(self.variables)-1:
                        var+="-"
                order.append(var)
           
            orders.append(order)
        return orders
    
    def get_all_models(self):
        self.solver.push()
        while self.solver.check() == sat:
            model = self.solver.model()

            block = []
            order = []
            for var in self.combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            self.all_orders.append(order)
      

            self.solver.add(Or(block))
       
        self.solver.pop()

    def create_z3_for_variables(self):
        for variable in self.variables:
            self.solver.add([And(1 <= self.z3_vectors[variable][index], self.num_variables >= self.z3_vectors[variable][index]) for index in range(self.sequence_length)])

   
    def create_z3_for_conditions(self):
        self.combined_conditions = [Int(f"C_{index + 1}") for index in range(self.sequence_length)]
        self.solver.add([Distinct(self.combined_conditions)])

    # get a specific ordering given constraints
    def eval(self):
        
       

        for i in range(self.sequence_length):
            count = len(self.z3_vectors)-1
            test = []
            for var in self.z3_vectors:
                exp = self.z3_vectors[var][i] * 10**count
                test.append(exp)
                count -= 1

            exp = add(test, None, len(test))
            self.solver.add(self.combined_conditions[i] == exp)

        print(self.solver)

        self.get_all_models()
        return self.encoding_to_name()




    
