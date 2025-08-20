# def set_rank(self, var, condition, rank, condition2):
#     x = BitVec("x", self.bitvectors.len)
#     y = BitVec("y", self.bitvectors.len)

#     if var not in self.rank_functions:
#         self.rank_functions[var] = Function(f'rank_{str(var)}', BitVecSort(self.bitvectors.determine_num_bits()), IntSort())
#         self.establish_ranking(var)

#     rank = self.rank_functions[var]
#     self.solver.add(
#         ForAll([x,y],
#             Implies(
#                 And(self.bitvectors.get_variable_assignment(var, x) == condition, 
#                     self.bitvectors.get_variable_assignment(var, y) == condition2),
#                 rank(x) > rank(y)
#             )
#         )
#     )

#  def establish_ranking(self, var):
#         orders = get_dim_variables(self.z3_variables, self.shape, 1)
#         n = self.n_trials()

#         for var in self.rank_functions:
#             rank = self.rank_functions[var]
#             for order in orders:
#                 self.solver.add([rank(order[i]) >= rank(order[i+1]) for i in range(n-1)])


    
    # def start_with(self, variable, condition):
    #     plans = shape_array(self.z3_variables, self.shape)
    #     arr = plans[:, 0]
    #     for z3 in arr:
    #         self.solver.add(self.bitvectors.get_variable_assignment(variable, z3) == condition)


    # def set_position(self, variable, condition, pos):
    #     plans = shape_array(self.z3_variables, self.shape)

    #     arr = plans[:, pos]
    #     for z3 in arr:
    #         self.solver.add(self.bitvectors.get_variable_assignment(variable, z3) == condition)
