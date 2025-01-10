from z3 import *
from .constraint import Constraint, Different, Match, Force, AllDifferent, OccurNTimes, AllMatch, Majority, Distinguish, NeverOccurTogether, AlwaysOccurTogether
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
        self.__num_z3_vars = np.prod(self.shape)
        self.solver = z3.Solver()
        self.translate = Translate()

        self.bitvectors = []
       
        self.create_z3_variables()
        self.constrain_z3_values()

    # you can come up with a better name
    def constrain_z3_values(self):
        """ for all of the z3 variables relating to a specific variable, 
         ensure that it can only be assigned to one of the levels
         of the specific variable """
        lower_bit = 0
   
        for variable in self.variables:
            # NOTE: z3 vectors is stored as a flattened array
            for index in range(self.__num_z3_vars):
                # NOTE: range(lo, hi) should give all levels of variable as int
                lo = 0
                hi = len(variable) - 1
                # required number of bits to encode a given value
                required_bits = int(math.ceil(math.log(variable.n, 2)))
       
                self.solver.add(
                        Or(
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
                            ),
                            # FIXME
                            And(
                                0 < Extract(
                                        lower_bit+required_bits, 
                                        lower_bit, 
                                        self.z3_conditions[index]
                                    ), 
                                -hi >= Extract(
                                    lower_bit+required_bits, 
                                    lower_bit, 
                                    self.z3_conditions[index]
                                )
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
        self.bitvectors = BitVectors(self.__num_z3_vars, self.variables)
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

            for arr in dim_variables:
                self.solver.add([Distinct(arr)])

        if isinstance(constraint, OccurNTimes):
            self.occur_exactly_n_times(constraint.n, constraint.reference_variable)


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
            print(count)
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



class AssignmentSolver(BitVecSolver):
    def __init__(self, shape, variables, blocks):
        BitVecSolver.__init__(self, shape, variables=variables)
        # shouldn't need separate assignment solver: get these from Assignment.unit_variables
        self.blocks = blocks
    
    
     # NOTE: won't generalize
    # FIXME: following compiler-style, maybe just translate all here
    # NOTE: should probably merge with regualr solver 
    def eval_constraint(self, constraint, dim = 0):

        assert isinstance(constraint, Constraint)

        if isinstance(constraint, AllMatch):
        
            num_members = self.shape[len(self.shape)-1]
            v = constraint.variable

            block_factor = constraint.wrt
            for i in range(num_members-1):
                factor_index = self.blocks.index(block_factor)
                self.eval_constraint(Match(i, i+1, v, factor = factor_index, level=constraint.level), dim)
                
        elif isinstance(constraint, Majority):
            dim2 = self.blocks.index(constraint.wrt)
            self.majority(dim, constraint.variable, constraint.condition, dim2, constraint.v)

        elif isinstance(constraint, Distinguish):
            dim = self.blocks.index(constraint.variable)
            self.distinguish(dim)

        elif isinstance(constraint, NeverOccurTogether):
            self.occur_together(dim, self.translate.no_values_match)

        elif isinstance(constraint, AlwaysOccurTogether):
            self.occur_together(dim, self.translate.values_match)

        else:
            super().eval_constraint(constraint, dim)

    # FIXME: look like majority 
    def distinguish(self, dim):
        # could you prettify this?
        levels = len(self.blocks[dim])
        for i in range(levels):
            arr_to_constrain = list(self.get_block(dim, i)[0])
            self.solver.add([Distinct(arr_to_constrain)])

    # this function checks how many times a value occurs accross all z3 vars in the matrix
    # move this to translate? 
    def counts(self, l, x, var):
        
        """ before decoupling """
        # test = []
        # for e in l: 
        #     # I really want to optimize this so we can reuse the lo and high values 
        #     val = self.bitvectors.get_variable_assignment(var, e)
        #     test.append(self.check_match(val, x))

        """ after decoupling """

        assignments = self.bitvectors.get_variable_assignments(var, l)
        return self.translate.counts(assignments, x)

#CSCW    PAPERS... NOTE: most of these were interviews and such
    # given two arrays, assert that no elements are the same between them


    def occur_together(self, dim, f):
        dim_variables = all_elements_of_dim(dim, self.z3_conditions, self.shape)
        # much easier to flatten this

        # expose this to the user ? 
        # is there a way to express this in z3
        for row1 in dim_variables:
            for val1 in row1:
                # iterating through every element in the matrix a second time 
                for row2 in dim_variables:
                    for val2 in row2:

                        if str(val1) != str(val2) and row1!=row2: 

                            __z3__ = self.translate.occur_together(val1, val2, row1, row2, f)
                            self.solver.add(__z3__)

    def get_block(self, dim, i):
        arr = np.array(shape_array(self.z3_conditions, self.shape))
        indexing = create_indexing_2(dim, self.shape)[i]
        block = arr[*indexing]
       
        shape = block.shape
  
        block = block.flatten()
        return block, shape


    def majority(self, ref, i, val, dim, variable):
        # this will apply to other constraints... how to modularize this?
   
        block, shape = self.get_block(dim, i)

        assert ref != dim

        if ref > dim: 
            ref -=1
    
        # ok, so this is 1 because now we only have 2 dimensions
        dim_variables = get_dim_variables(block, shape, ref)

        block = dim_variables

         # store the counts for each possible level in a variable 
        variable = self.variables.index(variable)
        var = self.variables[variable]
        

        # NOTE: the stalling problem is with count!
        # check the counts of every level and check that
        # they occur exactly n times
        for row in block:
            assignments = self.bitvectors.get_variable_assignments(var, row)
            __z3__ = self.translate.majority(row, val, assignments)
            self.solver.add(__z3__)

    # NOTE: this is kind of an axiom             
    def nested_assignment(self):
        participants = self.variables[0]
        # bit rage of pid 

        # NOTE: for this impl, make more efficient by checking entire 
        # bitvec at once rather than iterating attrs because we want 
        # all attrs to be the same
        for attr in self.variables[1:]:

            # for every pair of z3 variables, check that entire the bitvector 
            # is exactly the same if the pid matches
            for z3_var1 in self.z3_conditions:
                for z3_var2 in self.z3_conditions:
                    # bits representing pid
                    left = self.bitvectors.get_variable_assignment(participants, z3_var1)
                    right = self.bitvectors.get_variable_assignment(participants, z3_var2)
                    # bits representing attribute
                    l_attr = self.bitvectors.get_variable_assignment(attr, z3_var1)
                    r_attr = self.bitvectors.get_variable_assignment(attr, z3_var2)


                    __z3__ = self.translate.conditional(
                            self.translate.match(
                                left, 
                                right
                            ), 
                            self.translate.match(
                                l_attr, 
                                r_attr
                            )
                        )
                    # if the pid is the same, the attribute is the same 
                    self.solver.add(__z3__)

    # move this to translate (figure out what is important)
    def occur_exactly_n_times(self, n, variable):
        if n == 1:
            self.solver.add(
                self.translate.all_different(self.z3_conditions)
            )

        else: 
            num_levels = len(variable)
            assignments = self.bitvectors.get_variable_assignments(variable, self.z3_conditions)
            __z3s__ = self.translate.occur_exactly_n_times(n, num_levels, assignments)

            self.solver.add(And(__z3s__))


# NOTE: want to add wrt option for all constraints ?