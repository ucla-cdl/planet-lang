from z3 import *
import numpy as np
from .candl import *
from .helpers import *
from functools import reduce
from .bitvector import BitVectors
import itertools
import logging
import warnings

warnings.simplefilter('default')
logging.basicConfig(level=logging.DEBUG)


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
        self.bitvectors = []
       
        self.create_z3_variables()
        self.constrain_z3_values()
        self.distinguish_rows()

        self.rank_functions = {}
        self.ranks = {}

        self.logger = logging.getLogger(__name__)
 

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
    
    def block_columns(self, arr, width, stride=1):
        return np.array(arr)[:, 0:width:stride]

    def all_different(self, v=None, width = None, stride = 1):
        if v is None: 
            return
        # could you prettify this?
        dim_variables = get_dim_variables(self.z3_conditions, self.shape, 1)

        if width is not None:
            dim_variables = list(self.block_columns(dim_variables, width, stride))

        test = lambda x: [self.bitvectors.get_variable_assignment(z, x) for z in v]

        for arr in dim_variables:
            # FIXME (fixed but I'm not convinced)
            if v is not None:
                self.solver.add(distinct_or(list(map(test, arr))))
            else:
                self.solver.add(Distinct(arr))

    def n_trials(self):
        return self.shape[1]

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



    def establish_ranking(self, var):
        orders = get_dim_variables(self.z3_conditions, self.shape, 1)
        n = self.n_trials()

        for var in self.rank_functions:
            rank = self.rank_functions[var]
            for order in orders:
                self.solver.add([rank(order[i]) >= rank(order[i+1]) for i in range(n-1)])



    def count(self, l, x, f):
        test = []
        for e in l:
            test.append(If(f(e, x), 1, 0))
        return sum(test)
    

    def block_array(self, arr, block = []):
        return np.array(arr)[block[0][0]:block[0][1]:block[0][2], block[1][0]:block[1][1]:block[1][2]]
    
    def start_with(self, variable, condition):
        plans = np.array(get_dim_variables(self.z3_conditions, self.shape, 1))

        arr = plans[:, 0]
        for z3 in arr:
            self.solver.add(self.bitvectors.get_variable_assignment(variable, z3) == condition)


    def set_position(self, variable, condition, pos):
        plans = np.array(get_dim_variables(self.z3_conditions, self.shape, 1))

        arr = plans[:, pos]
        for z3 in arr:
            self.solver.add(self.bitvectors.get_variable_assignment(variable, z3) == condition)


    def set_rank(self, var, condition, rank, condition2):
        x = BitVec("x", self.bitvectors.len)
        y = BitVec("y", self.bitvectors.len)

        if var not in self.rank_functions:
            self.rank_functions[var] = Function(f'rank_{str(var)}', BitVecSort(self.bitvectors.determine_num_bits()), IntSort())
            self.establish_ranking(var)

        rank = self.rank_functions[var]
        self.solver.add(
            ForAll([x,y],
                Implies(
                    And(self.bitvectors.get_variable_assignment(var, x) == condition, 
                        self.bitvectors.get_variable_assignment(var, y) == condition2),
                    rank(x) > rank(y)
                )
            )
        )

    def absolute_rank(self, var, ranks):
        x = BitVec("x", self.bitvectors.len)

        orders = get_dim_variables(self.z3_conditions, self.shape, 1)
        n = self.n_trials()

        rank = Function(f'rank_{str(var)}', BitVecSort(self.bitvectors.determine_num_bits()), IntSort())
        for order in orders:
            self.solver.add([rank(order[i]) >= rank(order[i+1]) for i in range(n-1)])

        for condition in ranks:
            self.solver.add(
                ForAll([x],
                    Implies(
                        self.bitvectors.get_variable_assignment(var, x) == condition,
                        rank(x) == ranks[condition]
                    )
                )
            )
            

    def counterbalance(self, block=[], variables=None):
        """
        Apply counterbalancing to ensure equal occurrence of variable combinations.
        
        Args:
            block: List of blocks to apply (default empty list)
            variables: The variables to counterbalance (required)
            
        Returns:
            None: Modifies the solver in-place
        """
      
        # Get dimensional variables from z3 conditions
        plans = get_dim_variables(self.z3_conditions, self.shape, 1)
        

        # Apply blocks if provided
        if len(block):
            plans = self.block_array(plans, block)
        

        # Transpose the plans for processing
        plans = np.transpose(plans)

    

        # Initialize counts for tracking variable combinations
        counts = []
        
        # Define helper functions for value processing
        def get_possible_values(variable):
            """Return set of possible values for a variable (0 to len-1)"""
            return set(range(len(variable)))
        
        def test_assignment(variable, position):
            """Get variable assignment at the given position"""
            return self.bitvectors.get_variable_assignment(variable, position)
        
        # Generate all possible combinations of variable values
        value_combinations = list(itertools.product(
            *[get_possible_values(variable) for variable in variables]
        ))
        
        # Process each plan

        for plan_idx in range(len(plans)):
            # Map variables to their assignments in the current plan
            assignments = list(zip(*[
                list(map(lambda p: test_assignment(variable, p), plans[plan_idx])) 
                for variable in variables
            ]))
            
            # Count occurrences of each value combination
            for value_combo in value_combinations:
                # Define equality constraint function
                def check_equality(x, expected):
                    """Check if x equals expected for all indices"""
                    return And([expected[i] == x[i] for i in range(len(x))])
                
                # Count occurrences and store
                counts.append(self.count(assignments, value_combo, check_equality))
        
        # Add constraints to ensure equal counts for all combinations
        for i in range(len(counts)):
            for j in range(i+1, len(counts)):
                self.solver.add(counts[i] == counts[j])
                
    def match_block(self, variable, block = []):
        plans = get_dim_variables(self.z3_conditions, self.shape, 1)
        block = self.block_array(plans, block)

        flat_block = np.array(block).flatten()

        print(variable, block)

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
      
            for var in self.z3_conditions:
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
            for var in self.z3_conditions:
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
                __z3__ = self.bitvectors.get_variable_assignment(self.variables[j], self.z3_conditions[i])
                self.solver.add(__z3__ == condition)

    def check_model(self, model):
  
        self.solver.push()

        self.name_to_encoding(model, self.variables)
        result = self.solver.check()

        self.solver.pop()

        return result
