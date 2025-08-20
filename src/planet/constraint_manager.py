from planet.constraint import AbsoluteRank
from typing import Callable

class ConstraintManager:
    def __init__(self):
        self.constraints = []  # global list of all constraint instances
        self.rank_constraints = {}


    def add_absolute_rank(self, variable, condition, rank):
        if variable not in self.rank_constraints:
            constraint = AbsoluteRank(variable, condition, rank)
            self.rank_constraints[variable] = constraint
            self.constraints.append(constraint)
        else:
            constraint = self.rank_constraints[variable]
            constraint.add_rank(condition, rank)

        return constraint


    def add_constraint(self, constraint):
        # Avoid duplicates
        if self.has_constraint(constraint.variable, type(constraint)):
            return

        self.constraints.append(constraint)


    def get_constraints_for_variable(self, variable):
        return [
            c for c in self.constraints if c.variable == variable
        ]

    def has_constraint(self, variable, constraint_type):
        return any(
            isinstance(c, constraint_type) and c.variable == variable
            for c in self.constraints
        )
    
    def check_property(self, property:Callable):
        return any(property(c) for c in self.constraints)
    
    def stringified(self):
        return (str(c) for c in self.constraints)
    
    def get_constraints(self):
        return self.constraints
