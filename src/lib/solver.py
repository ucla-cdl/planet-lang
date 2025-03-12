from z3 import *
from .constraint import Constraint, Different, Match, Force, AllDifferent, OccurNTimes
import numpy as np
from .candl import *
from .helpers import *
from .translate import Translate
from functools import reduce
from .bitvector import BitVectors
import time


# NOTE: to decouple, should we have an ndarray class that 
# has z3 vars as special type? not sure if this infrastructure is necessary?

class BitVecSolver:
    def __init__(self, shape, variables):
        
        # how can we use translate without circular dependencies? 
        # some of these vars are related and should be stored together as a struct 
        self.shape = shape
        self.variables = variables
        self.num_z3_vars = np.prod(self.shape)
        self.solver = z3.Optimize()
        self.translate = Translate()

        self.bitvectors = []
       
        self.create_z3_variables()
        self.constrain_z3_values()
        self.distinguish_rows()

    # you can come up with a better name
    def constrain_z3_values(self):
        """ for all of the z3 variables relating to a specific variable, 
         ensure that it can only be assigned to one of the levels
         of the specific variable """
        lower_bit = 0
   
        for variable in self.variables:
            # NOTE: z3 vectors is stored as a flattened array
            for index in range(self.num_z3_vars):
                # NOTE: range(lo, hi) should give all levels of variable as int
                lo = 0
                hi = len(variable) - 1
                # required number of bits to encode a given value
                required_bits = int(math.ceil(math.log(variable.n, 2))) 
       
                self.solver.add(
               
                        And(
                            lo <= Extract(
                                    lower_bit+required_bits, 
                                    lower_bit, 
                                    self.z3_conditions[index]
                                ), 
                            hi >= Extract(
                                lower_bit+required_bits, 
                                lower_bit, 
                                self.z3_conditions[index]
                            )
                        )
                    
                        
                )


            # gives us index of the lower bit of the next variable
            lower_bit += required_bits + 1

        
    # FIXME: function that merges these
    # z3 variable for the overal condition assigned to a unit. 
    # for example, an n by n lating square has n*n z3 variables 
    # for each cell of the square. represented by the flattened array
    def create_z3_variables(self):
        self.bitvectors = BitVectors(self.num_z3_vars, self.variables)
        self.z3_conditions = self.bitvectors.get_variables()
    

    # NOTE: won't generalize
    # FIXME: following compiler-style, maybe just translate all here
    def eval_constraint(self, constraint, dim = 0):

        assert isinstance(constraint, Constraint)

        # how can we utilize transpose?
        if isinstance(constraint, Different):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()


            factor, level = constraint.get_level()
            dim_variables = get_dim_variables(self.z3_conditions, self.shape, dim, factor, level)
           
            for dim in dim_variables:

                left = self.bitvectors.get_variable_assignment(var, dim[i1])
                right = self.bitvectors.get_variable_assignment(var, dim[i2])

                __z3__ = self.translate.different(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Match):
     
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

            factor, level = constraint.get_level()

            dim_variables = get_dim_variables(self.z3_conditions, self.shape, dim, factor, level)

 
            for row in dim_variables:
                left = self.bitvectors.get_variable_assignment(var, row[i1])
                right = self.bitvectors.get_variable_assignment(var, row[i2])
                __z3__ = self.translate.match(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Force):
        
            var = constraint.get_variable()
            i = constraint.get_index()
            condition = constraint.get_condition() - 1

            dim_variables = all_elements_of_dim(dim, self.z3_conditions, self.shape)

            for dim in dim_variables:
                left = self.bitvectors.get_variable_assignment(var, dim[i])
                __z3__ = self.translate.match(left, condition)
            
                self.solver.add(__z3__)

        if isinstance(constraint, AllDifferent):
            # could you prettify this?
            dim_variables = get_dim_variables(self.z3_conditions, self.shape, dim)
            print(dim_variables[0][1])

            print(self.bitvectors.get_variable_assignment(self.variables[0], dim_variables[0][0]))
            
            self.solver.add(Distinct(self.bitvectors.get_variable_assignment(self.variables[0], dim_variables[0][0]), self.bitvectors.get_variable_assignment(self.variables[0], dim_variables[0][1])))

            test = lambda x: self.bitvectors.get_variable_assignment(self.variables[0], x)
            for arr in dim_variables:
                # self.solver.add([Distinct(list(map(test, arr)))])
                self.solver.add([Distinct(arr)])

        # if isinstance(constraint, Counterbalance):
        #     # shape array 
        #     # apply count to rows 
        #     print("fix me")

        if isinstance(constraint, OccurNTimes):
            self.occur_exactly_n_times(constraint.n, constraint.reference_variable)


    # NOTE: no rows can repeat in a given matrix 
    def distinguish_rows(self):
        plans = get_dim_variables(self.z3_conditions, self.shape, 1)

        for i in range(len(plans)):
            for j in range(len(plans)):

                if i != j:
                    assignment = []
                    for n in range(len(plans[j])):
                        assignment.append(plans[i][n] != plans[j][n])
          
                    self.solver.add(Or(assignment))

    def count(self, l, x):
        test = []
        for e in l:
            test.append(If(e == x, 1, 0))
        return sum(test)

    def counterbalance(self):
        plans = get_dim_variables(self.z3_conditions, self.shape, 0)
        counts = []
 
        possible_values = self.bitvectors.get_possible_values()
 
        for i in range(len(plans)):
            for v in possible_values:
                counts.append(self.count(plans[i], v))

        for i in range(len(counts)):
            for j in range(len(counts)):
                self.solver.add(counts[i] == counts[j])
                
    def match_block(self, block = []):
        plans = get_dim_variables(self.z3_conditions, self.shape, 1)
        block = np.array(plans)[block[0][0]:block[0][1], block[1][0]:block[1][1]]

        for z31 in np.array(block).flatten():
            for z32 in np.array(block).flatten():
                a1 = self.bitvectors.get_variable_assignment(self.variables[1], z31)
                a2 = self.bitvectors.get_variable_assignment(self.variables[1], z32)
                self.solver.add(a1==a2)

        # works when z3 representation is a matrix 
    def get_one_model(self):
        
        all_assignments = []
        t = time.time()
        if (self.solver.check() == sat):
            all_assignments = []
            model = self.solver.model()

      
            for var in self.z3_conditions:
                all_assignments.append(model.evaluate(model[var]))
        print(time.time() - t)

        
        return all_assignments
    
    # works when z3 rep iterates through many arrays
    # NOTE: should I merge these two functions?
    def get_all_models(self):
        all_orders = []
        self.solver.push()
        count = 0
        while self.solver.check() == sat:
            
            model = self.solver.model()

            block = []
            order = []
            for var in self.z3_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            all_orders.append(order)
            self.solver.add(Or(block))
            count+=1

        print(all_orders)
        self.solver.pop()
        return all_orders


    def encoding_to_name(self, all_orders, variables):
        # this makes life much easier
        z3_assignments = flatten_array(all_orders)
        num_vars = len(variables)
        
        orders = []
        for z3_assignment in z3_assignments:
            # this is an integer value, represented as a binary string
            assignment = int(str(z3_assignment))
            # this is where we will store the string rep of a condition
            # which is a concatination of it's variable assignments
            decoded_assignment = ""
 
            # # there is probably a more efficient way to do this
            for i in range(num_vars):
                # get the ith variable's assignment
                variable_assignment = assignment 
                # shift right variable assignment unitl desired var assignment 
                # is in the lower bits (+1 to account for two's compliment)
         
                for j in range(i):
                    variable_assignment >>= get_num_bits(len(variables[j])) + 1

                # get lower bits (associated with given variable)
                mask =  all_ones(get_num_bits(len(variables[i]))+ 1)
                variable_assignment &= mask

                # FIXME
                if variable_assignment >= len(variables[i]):
                    condition = "dropout"
                else:
              
                    # FIXME: this is silly, but need to inverse order to match array indexing
                    # variable_assignment = len(variables[i]) - 1 - variable_assignment
                    condition = variables[i].conditions[variable_assignment]

                # conder variable assignment to a string representation 
                decoded_assignment+=str(condition)

                # FIXME; hyphenate output for readability
                if i < len(variables)-1:
                    decoded_assignment+="-"

            orders.append(decoded_assignment)

        # return back in original form
        return shape_array(orders, np.array(all_orders).shape)
    
    def name_to_encoding(self, model, variables):

        # this makes life much easier
        model_assignments = flatten_array(model)
        num_vars = len(self.variables)
        
        for i in range(len(model_assignments)):
            assignment = model_assignments[i].split("-")

            # there is probably a more efficient way to do this
            for j in range(num_vars):
                # get the ith variable's assignment
                variable_assignment = assignment[j]
                condition = self.variables[j].condition_map[variable_assignment]
                __z3__ = self.bitvectors.get_variable_assignment(self.variables[j], self.z3_conditions[i])
                self.solver.add(__z3__ == condition)

    def check_model(self, model):
  
        self.solver.push()

        self.name_to_encoding(model, self.variables)
        result = self.solver.check()

        self.solver.pop()

        return result
