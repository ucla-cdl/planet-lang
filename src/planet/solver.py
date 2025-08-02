from z3 import *
import numpy as np
from .candl import *
from .helpers import *
from .bitvector import BitVectors
import itertools
import warnings
from itertools import combinations

class Solver: 
    def __init__(self, shape, variables):
        
        # how can we use translate without circular dependencies? 
        # some of these vars are related and should be stored together as a struct 
        self.shape = shape
        self.variables = variables
        self.solver = z3.Optimize()

class BitVecSolver(Solver):
    def __init__(self, shape, variables):
        super().__init__(shape, variables)
        self.bitvectors = BitVectors(np.prod(self.shape), self.variables)
        # NOTE: z3 vectors is stored as a flattened array
        self.z3_variables = self.bitvectors.get_variables()
        self.constrain_z3_values()
        self.distinguish_rows()

    # you can come up with a better name
    def constrain_z3_values(self):
        """ for all of the z3 variables relating to a specific variable, 
         ensure that it can only be assigned to one of the levels
         of the specific variable """
        for variable in self.variables:
            for index in range(np.prod(self.shape)):
                lo = 0
                hi = len(variable) - 1
                masked_bits = self.bitvectors.get_variable_assignment(variable, self.z3_variables[index])
                self.solver.add(
                        And(
                            lo <= masked_bits, 
                            hi >= masked_bits
                        )  
                )
  
    def get_partition(self, width, stride):
        dim_variables = shape_array(self.z3_variables, self.shape)
        if width is not None:
            dim_variables = partition_matrix_by_columns(dim_variables, width, stride)
        return dim_variables

    def all_different(self, variables=None, width = None, stride = 1):
        matrix = self.get_partition(width, stride)
        # This is necessary when the combinations of variables are unique, but
        # not the individual variables
        variable_assignment = lambda row: [self.bitvectors.get_variable_assignment(v, row) for v in variables]
        for row in matrix:
            self.solver.add(at_least_one_diff(list(map(variable_assignment, row))))
        
    def n_trials(self):
        return self.shape[1]

    # NOTE: no rows can repeat in a given matrix 
    def distinguish_rows(self):
        plans = shape_array(self.z3_variables, self.shape)
        for i, j in combinations(range(len(plans)), 2):
            # At least one assignment must differ
            self.solver.add(Or([a != b for a, b in zip(plans[i], plans[j])]))



    def slice_matrix(self, arr, block = []):
        def get_spec(block_data):
            return block_data[0], block_data[1], block_data[2]
        start_column, end_column, column_step = get_spec(block[0])
        start_row, end_row, row_step = get_spec(block[1])
        return np.array(arr)[start_column:end_column:column_step, start_row:end_row:row_step]


    def absolute_rank(self, var, ranks):
        design_matrix = shape_array(self.z3_variables, self.shape)
        n = self.n_trials()

        rank_fn = Function(f'rank_{str(var)}', BitVecSort(self.bitvectors.determine_num_bits()), IntSort())
        self.solver.add([rank_fn(plan[i]) >= rank_fn(plan[i+1]) for i in range(n-1) for plan in design_matrix])

        # for use in quantified expression
        x = self.bitvectors.new_bitvector()
        for condition, rank in ranks.items():
            # set the rank for every condition of the respective variable
            self.solver.add(
                ForAll([x],
                    Implies(
                        self.bitvectors.get_variable_assignment(var, x) == condition,
                        rank_fn(x) == rank
                    )
                )
            )
            
    def count(self, variables, condition, f):
        """
        if f returns true increase count by one for all variables
        """
        counts = [If(f(var, condition), 1, 0) for var in variables]
        return sum(counts)

    def counterbalance(self, block=[], variables=None):
        """
        Apply counterbalancing to ensure equal occurrence of variable combinations.
            
        Returns:
            None: Modifies the solver in-place
        """
        design_matrix = shape_array(self.z3_variables, self.shape)
        design_matrix = self.slice_matrix(design_matrix, block)
        design_matrix = np.transpose(design_matrix)
      
        # Generate all possible combinations of variable values
        possible_conditions = list(itertools.product(
            *[set(range(len(variable))) for variable in variables]
        ))
        
        counts = []
        for trials in design_matrix:
            masked_variables = list(zip(*[
                list(map(lambda z3_variable: self.bitvectors.get_variable_assignment(variable, z3_variable), trials)) 
                for variable in variables
            ]))
            
            check_equality = lambda variables, assignments: And([variables[i] == assignments[i] for i in range(len(variables))])
            counts.extend([self.count(masked_variables, condition, check_equality) for condition in possible_conditions])
        
        # Add constraints to ensure equal counts for all combinations
        for i in range(len(counts)):
            for j in range(i+1, len(counts)):
                self.solver.add(counts[i] == counts[j])

   
    def match_block(self, variable, block = []):
        plans = shape_array(self.z3_variables, self.shape)
        block = self.slice_matrix(plans, block)

        flat_block = np.array(block).flatten()
        for i in range(len(flat_block)):
            for j in range(i, len(flat_block)):
                a1 = self.bitvectors.get_variable_assignment(variable, flat_block[i])
                a2 = self.bitvectors.get_variable_assignment(variable, flat_block[j])
                self.solver.add(a1==a2)

        # works when z3 representation is a matrix 
    def get_one_model(self):
        all_assignments = []
    
        if (self.solver.check() == sat):
            all_assignments = []
            model = self.solver.model()
      
            for var in self.z3_variables:
                all_assignments.append(model.evaluate(model[var]))
 
        return all_assignments
    
    # works when z3 rep iterates through many arrays
    # NOTE: should I merge these two functions?
    def get_all_models(self):
        all_orders = []
        self.solver.push()
        count = 0
        capacity = 10000
        while self.solver.check() == sat and count < capacity:
            model = self.solver.model()
            block = []
            order = []
            for var in self.z3_variables:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            all_orders.append(order)
            self.solver.add(Or(block))
            count+=1
        if self.solver.check() == sat:
            warnings.warn(f"There are more orders not captured in the model due order capacity (currently set to {capacity})")

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
    
    def name_to_encoding(self, model):

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
                __z3__ = self.bitvectors.get_variable_assignment(self.variables[j], self.z3_variables[i])
                self.solver.add(__z3__ == condition)

    def check_model(self, model):
  
        self.solver.push()

        self.name_to_encoding(model, self.variables)
        result = self.solver.check()

        self.solver.pop()

        return result
