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
        self.shape = shape
        self.variables = variables
        self.solver = z3.Optimize()

class BitVecSolver(Solver):
    def __init__(self, shape, variables):
        """
        Solver using Z3 BitVectors for combinatorial designs.
        Automatically sets up BitVectors and enforces row uniqueness.
        """
        super().__init__(shape, variables)
        self.bitvectors = BitVectors(np.prod(self.shape), self.variables)
        self.z3_variables = self.bitvectors.get_variables()
        self.constrain_z3_values()
        self.distinguish_rows()

    # you can come up with a better name
    def constrain_z3_values(self):
        """
        Enforce that each Z3 variable can only take a valid level
        based on its corresponding experimental variable.
        """
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
        """
        Partition the design matrix by columns if width is specified.

        Args:
            width (int): Number of columns per partition.
            stride (int): Step size between partitions.

        Returns:
            np.ndarray: Partitioned design matrix.
        """
        dim_variables = shape_array(self.z3_variables, self.shape)
        if width is not None:
            dim_variables = partition_matrix_by_columns(dim_variables, width, stride)
        return dim_variables

    def all_different(self, variables=None, width = None, stride = 1):
        """
        Enforce that for each row in the partitioned matrix, 
        all combinations of the selected variables differ in at least one position.
        """
        matrix = self.get_partition(width, stride)
        
        for row in matrix:
            row_assignments = [
                [self.bitvectors.get_variable_assignment(v, r) for v in variables] 
                for r in row
            ]
            self.solver.add(at_least_one_diff(row_assignments))
        
    def n_trials(self):
        return self.shape[1]

    # NOTE: no rows can repeat in a given matrix 
    def distinguish_rows(self):
        plans = shape_array(self.z3_variables, self.shape)
        plan_encodings = []

        for plan in plans:
            # Concatenate all variables in the row into one BitVec
            plan_bits = plan[0]
            for var in plan[1:]:
                plan_bits = Concat(plan_bits, var)
            plan_encodings.append(plan_bits)

        # Enforce that all rows are distinct
        self.solver.add(Distinct(*plan_encodings))


    def slice_matrix(self, arr, block = []):
        # Unpack block and slice matrix
        (start_col, end_col, col_step), (start_row, end_row, row_step) = block
        return np.array(arr)[start_col:end_col:col_step, start_row:end_row:row_step]


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
