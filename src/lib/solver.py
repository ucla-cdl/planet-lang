from z3 import *
from .constraint import Constraint, Different, Match, Force, AllDifferent, OccurNTimes
import numpy as np
from .candl import *
from .helpers import *
from .translate import Translate
from functools import reduce

class Solver:
    def __init__(self, shape, variables):
        self.shape = shape
        self.variables = variables
        self.__num_z3_vars = np.prod(self.shape)
        self.solver = z3.Solver()
        self.translate = Translate()

        self.construct_z3_variable()
        self.constrain_z3_values()
        self.create_z3_for_conditions()
        self.constrain_z3_conditions()

    # you can come up with a better name
    def constrain_z3_values(self):
        # for all of the z3 variables relating to a specific variable, 
        # ensure that it can only be assigned to one of the levels
        # of the specific variable
        for variable in self.variables:
            # NOTE: z3 vectors is stored as a flattened array
            for index in range(self.__num_z3_vars):
                self.solver.add(
                        And(
                            1 <= self.z3_vectors[variable][index], 
                            variable.n >= self.z3_vectors[variable][index]
                        ) 
                )

    def z3_of_same_type(self, label, n):
        return [Int(f"{label}_{index + 1}") for index in range(n)]

    # FIXME: function that merges these
    # z3 variable for the overal condition assigned to a unit. 
    # for example, an n by n lating square has n*n z3 variables 
    # for each cell of the square. represented by the flattened array
    def create_z3_for_conditions(self):
        self.z3_conditions = self.z3_of_same_type("C", self.__num_z3_vars)
    
    # NOTE: using to same for z3 variables
    # I think I want to do this in assignment. (ie. assign conditions to sequence)

    # it appears that the above function is closely related to this one...
    def construct_z3_variable(self):
        z3_vectors = {}
        for variable in self.variables:
            z3_vectors[variable] = self.z3_of_same_type(str(variable), self.__num_z3_vars)
            
            [Int(f"{str(variable)}_{index + 1}") for index in range(self.__num_z3_vars)]
            
        self.z3_vectors = z3_vectors
    
    # conditions are a combination of variable assignments
    # constrain conditions based on variable constraints
    def constrain_z3_conditions(self):
        # flattened representation
        for i in range(self.__num_z3_vars):
            # start at the last index because the first variable
            # is the number closest to the left in the variable name
            place = len(self.z3_vectors)-1
            numbers = []
            for var in self.z3_vectors:
                num = self.z3_vectors[var][i] * 10**place
                numbers.append(num)
                place -= 1

            # this adds all of the numbers in the array
            # I could've used numpy... whoops
            combined_number = add(numbers, None, len(numbers))

            # constrain z3 variable s.t. it is the concatination
            # of the assigned values to it's respective variables
            self.solver.add(self.z3_conditions[i] == combined_number)

        # NOTE: won't generalize
    # FIXME: following compiler-style, maybe just translate all here
    def eval_constraint(self, constraint, dim = 0):
        assert isinstance(constraint, Constraint)
        # this is perhaps a little wonky...
        # not sure if the loop unrolling should happen in 
        # the constraint class...
        dim_indexings = create_indexing(dim, self.shape)
        
        # how can we utilize transpose?
        if isinstance(constraint, Different):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

            dim_variables = []
            for indexing in dim_indexings:
                dim_variables.append(np.array(self.z3_vectors[var]).reshape(self.shape)[*indexing].tolist())
    
            for row in dim_variables:
                left = row[i1]
                right = row[i2]
                __z3__ = self.translate.different(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Match):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

            dim_variables = []
            for indexing in dim_indexings:
                dim_variables.append(np.array(self.z3_vectors[var]).reshape(self.shape)[*indexing].tolist())
    
            for row in dim_variables:
                left = row[i1]
                right = row[i2]
                __z3__ = self.translate.match(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Force):
            var = constraint.get_variable()
            i = constraint.get_index()
            condition = constraint.get_condition()

            dim_variables = []
            for indexing in dim_indexings:
                dim_variables.append(np.array(self.z3_vectors[var]).reshape(self.shape)[*indexing].tolist())
    
            for row in dim_variables:
                left = row[i]
                __z3__ = self.translate.match(left, condition)
                self.solver.add(__z3__)

        if isinstance(constraint, AllDifferent):
            # could you prettify this?
            z3_with_shape = shape_array(self.z3_conditions, self.shape)
            for indexing in dim_indexings:
                arr_to_constrain = np.array(z3_with_shape)[*indexing].tolist()
                self.solver.add([Distinct(arr_to_constrain)])

    def all_different(self):
        self.solver.add(Distinct(self.z3_conditions))

        # works when z3 representation is a matrix 
    def get_one_model(self):
        all_assignments = []

        if (self.solver.check() == sat):
            model = self.solver.model()

            for var in self.z3_conditions:
                all_assignments.append(model.evaluate(model[var]))

        return all_assignments
    
    # works when z3 rep iterates through many arrays
    # NOTE: should I merge these two functions?
    def get_all_models(self):
 
        all_orders = []
        self.solver.push()

        while self.solver.check() == sat:
            model = self.solver.model()

            block = []
            order = []
            for var in self.z3_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            all_orders.append(order)
            self.solver.add(Or(block))

        self.solver.pop()
        return all_orders




class BitVecSolver:
    def __init__(self, shape, variables):

        self.shape = shape
        self.variables = variables
        self.__num_z3_vars = np.prod(self.shape)
        self.solver = z3.Solver()
        self.translate = Translate()
        self.bitvec_length = self.determine_num_bits()
       
        self.create_z3_for_conditions()
        self.constrain_z3_values()

    def determine_num_bits(self):
        bitvec_length = 0
        for variable in self.variables:
            bits = int(round(math.log(variable.n, 2)))
            bitvec_length += bits

        # necessary for two's compliment bit
        bitvec_length += len(self.variables)
        return bitvec_length
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
                required_bits = int(round(math.log(variable.n, 2)))
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
    def create_z3_for_conditions(self):
        self.z3_conditions =  [BitVec(f"C_{index + 1}", self.bitvec_length) for index in range(self.__num_z3_vars)]
    
    def get_lower_bits(self, var):
        var_index = self.variables.index(var)
        bit_index = 0
        # for all the variables already represented
        for i in range(var_index):
            # length of all of the other variable bit representations
            bit_index += get_num_bits(len(self.variables[i]))

        # accounts for two's compliment bit
        bit_index += var_index
        return bit_index

    # NOTE: won't generalize
    # FIXME: following compiler-style, maybe just translate all here
    def eval_constraint(self, constraint, dim = 0):

        assert isinstance(constraint, Constraint)

        # how can we utilize transpose?
        if isinstance(constraint, Different):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

            dim_variables = all_elements_of_dim(dim, self.z3_conditions, self.shape)
            
           
            lo = self.get_lower_bits(var)
            length = get_num_bits(len(var))

            
            for dim in dim_variables:

                left = Extract(lo+length, lo, dim[i1])
                right = Extract(lo+length, lo, dim[i2])
                __z3__ = self.translate.different(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Match):
            var = constraint.get_variable()
            i1 = constraint.get_index_to_match()
            i2 = constraint.get_index()

            dim_variables = all_elements_of_dim(dim, self.z3_conditions, self.shape)
           
            lo = self.get_lower_bits(var)
            length = get_num_bits(len(var))
 
            for row in dim_variables:
                left = Extract(lo+length, lo, row[i1])
                right = Extract(lo+length, lo, row[i2])
                __z3__ = self.translate.match(left, right)
                self.solver.add(__z3__)

        if isinstance(constraint, Force):
        
            var = constraint.get_variable()
            i = constraint.get_index()
            condition = constraint.get_condition()
            condition -= 1

            dim_variables = all_elements_of_dim(dim, self.z3_conditions, self.shape)


            lo = self.get_lower_bits(var)
            length = get_num_bits(len(var))

        
            for dim in dim_variables:
                left = Extract(length+lo, lo, dim[i])
                __z3__ = self.translate.match(left, condition)
            
                self.solver.add(__z3__)

        if isinstance(constraint, AllDifferent):
            # could you prettify this?
            dim_indexings = create_indexing(dim, self.shape)
    
    
            for indexing in dim_indexings:
                arr_to_constrain = get_elements_of_dim(self.z3_conditions, self.shape, indexing)
       
                self.solver.add([Distinct(arr_to_constrain)])

        if isinstance(constraint, OccurNTimes):
            self.occur_exactly_n_times(constraint.n)


        # works when z3 representation is a matrix 
    def get_one_model(self):
        all_assignments = []

        if (self.solver.check() == sat):
            model = self.solver.model()
            for var in self.z3_conditions:
                all_assignments.append(model.evaluate(model[var]))
        
        return all_assignments
    
    # works when z3 rep iterates through many arrays
    # NOTE: should I merge these two functions?
    def get_all_models(self):
        all_orders = []
        self.solver.push()

        while self.solver.check() == sat:
            
            model = self.solver.model()

            block = []
            order = []
            for var in self.z3_conditions:
                block.append(var != model[var])
                order.append(model.evaluate(model[var]))

            all_orders.append(order)
            self.solver.add(Or(block))

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
    

class AssignmentSolver(BitVecSolver):
    def __init__(self, shape, variables):
        BitVecSolver.__init__(self, shape, variables=variables)

    # should move these to constraints file and inherit from constraint
    # for now use this to test :)
    def all_different(self):
        self.solver.add(Distinct(self.z3_conditions))

    def distinguish(self, dim):
        # could you prettify this?
        dim_indexings = create_indexing_2(dim, self.shape)

        for indexing in dim_indexings:
            arr_to_constrain = get_elements_of_dim(self.z3_conditions, self.shape, indexing)
            arr_to_constrain = flatten_array(arr_to_constrain)
 
            self.solver.add([Distinct(arr_to_constrain)])

    # this function checks how many times a value occurs accross all z3 vars in the matrix
    def count(self, l, x, var):
        test = []
        lo = self.get_lower_bits(var)
        length = get_num_bits(len(var))
        for e in l: 
            val = Extract(length+lo, lo, e)
            test.append(If(val == x, 1, 0))

        return sum(test)


    # given two arrays, assert that no elements are the same between them
    def no_values_match(self, arr1, arr2):
        constraints = []
        for val1 in arr1:
            for val2 in arr2:
                constraints.append( val1 != val2)
        return And(constraints)

    # assert that two values are the same
    def foo(self, val1, val2):
        return val1 == val2

    def never_occur_together(self, dim):
        dim_variables = all_elements_of_dim(dim, self.z3_conditions, self.shape)
        # much easier to flatten this
        for row1 in dim_variables:
            for val1 in row1:
                # iterating through every element in the matrix a second time 
                for row2 in dim_variables:
                    for val2 in row2:

                        if str(val1) != str(val2) and row1!=row2:

                            # FIXME: the array without the values we check for equality 
                            arr1 = row1[:]
                            arr1.pop(arr1.index(val1))
                            arr2 = row2[:]
                            arr2.pop(arr2.index(val2))

                            # if two variables are equal, no values in their 
                            # respective rows can be equal 
                            self.solver.add(
                                Implies(
                                 
                                    self.foo(
                                        val1, 
                                        val2
                                    ), 
                                    self.no_values_match(
                                        arr1, 
                                        arr2
                                    )
                        
                                    )
                                )
                            


    def majority(self, i, val, dim):

        arr = np.array(shape_array(self.z3_conditions, self.shape))
        indexing = create_indexing_2(dim, self.shape)[i]
        block = arr[*indexing]
        d1 = int(reduce(lambda x, y: x * y, block.shape) / block.shape[len(block.shape) - 1])
        shape = (d1, block.shape[len(block.shape) - 1])
  
        block = block.flatten()
        block = list(np.array(block).reshape(shape))

         # store the counts for each possible level in a variable
        num_levels = len(self.variables[1])
        g = Function("g", IntSort(), IntSort(), IntSort())

        # NOTE: the stalling problem is with count!
        # check the counts of every level and check that
        # they occur exactly n times
        for row in block:
            for x in range(num_levels):
                for j in range(len(block)):
                    self.solver.add(g(j, x) == self.count(block[j], x, self.variables[1]))

                    if x == val:
                        self.solver.add(g(j, val) > int(len(row)/2))
                            
    def nested_assignment(self):
        var = self.variables[0]
        attr = self.variables[1]

        lo = self.get_lower_bits(var)
        length = get_num_bits(len(var))

        lo_attr = self.get_lower_bits(attr)
        length_attr = get_num_bits(len(attr))

        for c1 in self.z3_conditions:
            for c2 in self.z3_conditions:
               left = Extract(lo+length, lo, c1)
               right = Extract(lo+length, lo, c2)

               l_attr = Extract(lo_attr+length_attr, lo_attr, c1)
               r_attr = Extract(lo_attr+length_attr, lo_attr, c2)
               self.solver.add(
                   Implies(
                       left == right,
                        l_attr == r_attr
                   )
               )

    def occur_exactly_n_times(self, n):
        if n == 1:
            self.all_different()

        else: 
            # store the counts for each possible level in a variable
            num_levels = len(self.variables[0])
            f = Function("f", IntSort(), IntSort())

            # NOTE: the stalling problem is with count!

            # check the counts of every level and check that
            # they occur exactly n times
            for x in range(0, num_levels):
                self.count(self.z3_conditions, x, self.variables[0])
                self.solver.add(f(x) == self.count(self.z3_conditions, x, self.variables[0]))
                self.solver.add(Or(f(x) == n, f(x) == 0))