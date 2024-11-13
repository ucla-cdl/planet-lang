from z3 import *
from .helpers import *
from .orders import Sequence
from .narray import *
import numpy as np
from .variable import ExperimentVariable
from .constraint import Different, Match, Constraint, Force, AllDifferent

class Assignment:
    """The assignment class matches each unit to an order of conditions.

    units: a list of unit objects 
    conditions_per_unit: how many experimental conditions does each unit witness/experience
    possible_orders: an object that maintains information about the possible 
        orderings of experimental condiitons, and the user-defined constraints
        on which conditions must/can appear in different positions in the order
    """
    def __init__(self):
        self.units = np.array([])

        self.unit_options = None
        self.treatments = None
        self.unit_variables = []
        self.constraints = []

        self.variables = []

        self.solver = z3.Solver()
        self.z3_vectors = []

        self.block_constraints = []


    def assign_conditions(self, subjects, variables=[], blocks = []):
        pass

    def assign_to_sequence(self, subjects, sequence, variables = []):

        assert isinstance(sequence, Sequence)
        self.dims = [subjects.n, sequence.n]
        self.unit_variables = [subjects, sequence]
        self.variables = variables
        self.num_variables = len(self.variables) # num indep vars in experiment
        self.sequence = sequence
  

    # ensure that we distinguish this
    def recieve_different_conditions(self, block):
        # create constraint object... want lazy eval of this
        r = self.unit_variables[0]
    
        # I want this instead to return a constraint condition :)
        if block == r:
            self.block_constraints.append(AllDifferent(block))
        

    def constrain_z3_values(self):
        for variable in self.variables:
            self.solver.add(
                [
                    And(
                        1 <= self.z3_vectors[variable][index], 
                        variable.n >= self.z3_vectors[variable][index]
                    ) 
                for index in range(self.__num_z3_vars)])

  
    def create_z3_for_conditions(self):
        # same for all any variables
        return [Int(f"C_{index + 1}") for index in range(self.__num_z3_vars)]
    
    # NOTE: using to same for z3 variables
    # I think I want to do this in assignment. (ie. assign conditions to sequence)
    def construct_z3_variable(self, variables):
        z3_vectors = {}
        for variable in variables:
            z3_vectors[variable] = [Int(f"{str(variable)}_{index + 1}") for index in range(self.__num_z3_vars)]
        self.z3_vectors = z3_vectors


    
    # equvilant to above
    # conditions are a combination of variable assignments
    def constrain_z3_conditions(self, seq, combined_conditions):
        print("here", combined_conditions)
        for i in range(len(seq)):
            count = len(self.z3_vectors)-1
            test = []
            for var in self.z3_vectors:
                exp = self.z3_vectors[var][i] * 10**count
                test.append(exp)
                count -= 1

            exp = add(test, None, len(test))

            self.solver.add(combined_conditions[i] == exp)


    def get_all_models(self, seq, units, combined_conditions):
        count = 0
        while self.solver.check() == sat and count < units.n:
            model = self.solver.model()

            block = []
            order = []
            for var in combined_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            # move this pls, to this class, not seq
            seq.all_orders.append(order)
      
            # if this is And, we get a latin square
            test = Or(block)
            for constraint in self.constraints:
                if isinstance(constraint, AllDifferent):
                    test = And(block)
                    break

            self.solver.add(test)
            count += 1

        return seq.all_orders

    def get_one_model(self, combined_conditions):
        if (self.solver.check() == sat):
            model = self.solver.model()
            return np.array([[model[combined_conditions[i]]] for i in range(len(combined_conditions))]).reshape(self.units.shape)

    # probably should just be a class
    def encoding_to_name(self, all_orders):
  
        orders = []
        r = len(all_orders)
        c = len(all_orders[0])
        num_vars = len(self.variables)
        for i in range(r):
            order = []
            for j in range(c):
                # efficiently get first elem?
                var = ""
                for v in range(num_vars):
                    x = int(str(all_orders[i][j])[v])-1
                    var+=str(self.variables[v].conditions[x])
                    if v < len(self.variables)-1:
                        var+="-"
                order.append(var)
           
            orders.append(order)

        return orders
    
    def eval_constraint(self, constraint):

        assert isinstance(constraint, Constraint)

        if isinstance(constraint, Different) or isinstance(constraint, Match) or isinstance(constraint, Force):
            self.solver.add(constraint.eval_constraint(self.z3_vectors))
        if isinstance(constraint, AllDifferent):
            self.constraints.append(constraint)

    # somehow merge eval and generate
    def eval(self):

        # shape should be 1-d array
        subjects = self.unit_variables[0]
        if len(self.block_constraints) > 0:
            shape = (subjects.n, self.sequence.n)
        else:
            # 1 dim array
            shape = (1, self.sequence.n)

        # to referent shape later on
        self.units = np.ndarray(shape)
        self.shape = self.units.shape
        self.__num_z3_vars = len(self.units.flatten().tolist())
        # so we can pass to functions the same as the array
        # when referencing all units

        # I want lazy eval of this 
        # make this the same as in generate... we want to generalize the 
        # creation of these so there aren't two different functions
        self.construct_z3_variable(self.variables)

        units = self.unit_variables[0]
        seq = self.unit_variables[1]

        assert isinstance(seq, Sequence)

        # ok, so we know we can postpone the eval of this 
        # why am I passing a class-variable?
        # seq.construct_z3_variable(seq.variables)
        # self.construct_z3_variable(self.variables)
        # do the loop in seq though
        for constraint in seq.constraints:
            self.eval_constraint(constraint)

        self.constrain_z3_values()
        combined_conditions = self.create_z3_for_conditions()
        combined_conditions_arr = np.array(combined_conditions).reshape(self.units.shape).tolist()

        for row in combined_conditions_arr:
            self.solver.add([Distinct(row)])

        # distinguish columns
        if len(self.block_constraints) > 0:
            for i in range(len(combined_conditions_arr[0])):
                self.solver.add([Distinct(np.array(combined_conditions_arr)[:, i].tolist())])
        

        combined_conditions_flat = np.array(combined_conditions).flatten().tolist()
        self.constrain_z3_conditions(combined_conditions_flat, combined_conditions_flat)

        

        if len(self.block_constraints) > 0:
            test = self.get_one_model(combined_conditions)
            return np.array(self.encoding_to_name(test.tolist()))
        else: 
            test = self.get_all_models(seq, units, combined_conditions)
            return np.array(self.encoding_to_name(test))

        

    
      