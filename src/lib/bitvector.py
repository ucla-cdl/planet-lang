from z3 import *
from .candl import *

class BitVectors:
    def __init__(self, n, variables):
        self.variables = variables
        self.len = self.determine_num_bits()
        self.z3_representation =  [BitVec(f"C_{index + 1}", self.len) for index in range(n)]
        
        

    def determine_num_bits(self):
        bitvec_length = 0
        for variable in self.variables:
            bits = int(math.ceil(math.log(variable.n, 2)))
            bitvec_length += bits

        # necessary for two's compliment bit
        bitvec_length += len(self.variables)
        return bitvec_length
    

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
        return self.z3_representation
    
    def get_variable_assignment(self, var, z3):
        lo = self.get_lower_bits(var)
        length = get_num_bits(len(var))
        return Extract(lo+length, lo, z3)
    
    def get_variable_assignments(self, var, z3s):
        
        assignments = []

        for z3 in z3s:
            assignments.append(self.get_variable_assignment(var, z3))

        return assignments

