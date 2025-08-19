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

