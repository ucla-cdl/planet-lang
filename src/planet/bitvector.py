from z3 import *
from .candl import *

class BitVectors:
    def __init__(self, n, variables):
        self.variables = variables
        self.len = self.determine_num_bits()
        self.z3_variables =  [BitVec(f"C_{index + 1}", self.len) for index in range(n)]

    def get_possible_values(self):
        values = []
        k = 0
        for i in range(len(self.variables)):
            variable = self.variables[i]
            n = variable.n

            if not i:
                values.extend([x for x in range(n)])
            else:
                k += int(math.ceil(math.log(self.variables[i-1].n, 2))) + 1

                new_values = []
                for v in values:
                    for y in range(n):
                        x = y << k 
             
                        new_values.append(x + v)
                
                values.extend(new_values)

            if not len(values):
                values.extend([x for x in range(n)])

        return set(values)
    
    def determine_num_bits_total(self):
        bitvec_length = 0
        for variable in self.variables:
            bits = int(math.ceil(math.log(variable.n, 2)))
            bitvec_length += bits

        # necessary for two's compliment bit
        bitvec_length += len(self.variables)
        return bitvec_length
    
    def determine_num_variable_bits(self, variable):
        return int(math.ceil(math.log(variable.n, 2)))

    def determine_num_bits(self, variable=None):

        if variable is None:
            return self.determine_num_bits_total()
        else:
            return self.determine_num_variable_bits(variable)

    

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
    
    def get_variables(self):
        return self.z3_variables
    
    def get_variable_assignment(self, var, z3):
        lo = self.get_lower_bits(var)
        length = get_num_bits(len(var))
        return Extract(lo+length, lo, z3)

    
    def get_variable_assignments(self, var, z3s):
        assignments = []

        for z3 in z3s:
            assignments.append(self.get_variable_assignment(var, z3))

        return assignments
    
    def new_bitvector(self):
        # FIXME: hacky
        return BitVec("x", self.len)
    
    def int_as_bitvec(self, val, size):
        return BitVecVal(val, size)
    

class TupleVariables:
    def __init__(self, n, variables):
        """
        Initialize the TupleVariables class.

        Args:
            n (int): The number of Z3 tuple variables to create.
            variables (list): A list of ExperimentVariable objects.
        """
        self.variables = variables
        self.tuple_sort, self.tuple_ctor, self.tuple_proj = TupleSort("IntTuple", [IntSort() for _ in variables])
        self.z3_variables = [Const(f"C_{index + 1}", self.tuple_sort) for index in range(n)]

    def get_possible_values(self):
        """
        Get all possible values for the tuple variables.

        Returns:
            set: A set of Z3 tuples representing all possible values.
        """
        values = []
        for variable in self.variables:
            n = variable.n
            values.append([x for x in range(n)])
        return set(product(*values))  # Cartesian product of all variable values

    def get_variables(self):
        """
        Get the Z3 tuple variables.

        Returns:
            list: A list of Z3 tuple variables.
        """
        return self.z3_variables
    
    def tuple_to_int(self, t):
        n = len(self.tuple_proj)
        return Sum([
            self.tuple_proj[i](t) * (10 ** (n - i - 1))
            for i in range(n)
        ])
    

    def get_variable_assignment(self, var, z3_tuple):
        """
        Extract the assignment for a specific variable from a Z3 tuple.

        Args:
            var (ExperimentVariable): The variable to extract.
            z3_tuple (Z3 tuple): The Z3 tuple variable.

        Returns:
            z3.Int: The Z3 integer representing the variable's assignment.
        """
        var_index = self.variables.index(var)
        return self.tuple_proj[var_index](z3_tuple)

    def get_variable_assignments(self, var, z3_tuples):
        """
        Extract the assignments for a specific variable from a list of Z3 tuples.

        Args:
            var (ExperimentVariable): The variable to extract.
            z3_tuples (list): A list of Z3 tuple variables.

        Returns:
            list: A list of Z3 integers representing the variable's assignments.
        """
        return [self.get_variable_assignment(var, z3_tuple) for z3_tuple in z3_tuples]



    # def new_tuple_variable(self, name):
    #     """
    #     Create a new Z3 tuple variable.

    #     Args:
    #         name (str): The name of the Z3 tuple variable.

    #     Returns:
    #         Z3 tuple: A new Z3 tuple variable.
    #     """
    #     return self.create_z3_tuple(name)

    # def int_as_tuple(self, values):
    #     """
    #     Convert a list of integers into a Z3 tuple constant.

    #     Args:
    #         values (list): A list of integer values.

    #     Returns:
    #         Z3 tuple: A Z3 tuple constant.
    #     """
    #     return self.tuple_sort.constructor(*[IntVal(value) for value in values])