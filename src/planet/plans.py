from dataclasses import dataclass, field
import hashlib
from planet.designer import Designer
import math
from planet.randomizer import Randomizer


class PlanGenerator:
    def __init__(self, design, num_units):
        self.design = design
        self.random_variables = design.identify_random_vars()
        self.num_units = num_units

    def instantiate_random_variables(self, n, rand, plans):
        # NOTE to self: this will only work if there is one random variable :)
        """
        Think about this like instantiating the elements of a matrix of random variables
        """
        assert plans is not None
        width = self.design.design_variables[rand].get_width(self.design.get_width())
        span = self.design.design_variables[rand].get_span()
        variables = rand.get_variables()

        random_index = self.design.variables.index(variables[0])
        randomizer = Randomizer(rand, width, span, int(n*self.design.get_width()/width/span))
        return randomizer.apply_randomization(width, span, random_index, n, plans)

    def generate(self):
        self.design.designer.start(self.design)
        plans = self.design.designer.eval()

        if not plans.any():
            raise ValueError("This design results in no viable plans. Consider a new design.")
     
        # problem identifying random vars
        n = math.ceil(self.num_units / len(plans)) * len(plans)


        for rand in self.random_variables:
            plans = self.instantiate_random_variables(n, rand, plans)

        return plans
   
