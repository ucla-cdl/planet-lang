from z3 import *
from .helpers import *

class Assignment:
    """The assignment class matches each unit to an order of conditions.

    units: a list of unit objects 
    conditions_per_unit: how many experimental conditions does each unit witness/experience
    possible_orders: an object that maintains information about the possible 
        orderings of experimental condiitons, and the user-defined constraints
        on which conditions must/can appear in different positions in the order
    """
    def __init__(self, units, conditions_per_unit = 1, groups = None):
        self.groups = groups
        self.conditions_per_unit = conditions_per_unit
        self.units = units

        orders = self.groups.eval()
        count = 1
        for order in orders:
            print(f"order {count}: {order}")

    # assigns specifies unit to one possible ordering (randomly determined given constraints)
    def assign_unit(self, n):
        unit = self.units[n]
        print("assignment")
        print(self.groups.eval())
        

    
      