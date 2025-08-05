from planet.candl import generate_conditions
from planet.constraint import InnerBlock, OuterBlock
from planet.variable import MultiFactVariable



class Randomizer:
    def __init__(self, variable, width, span, n):
        self.rand_vars = self._generate_random_variables(n, variable, width)
        self.n = n
        self.variable = variable
        self.width = width
        self.span = span

      
    def _determine_random_width(self, rand):
        width = self.get_width()
        div = 1
        for constraint in self.constraints.get_constraints_for_variable(rand):
            if isinstance(constraint, OuterBlock):
                width = constraint.width
  
            elif isinstance(constraint, InnerBlock):
                div = constraint.width
        
        return int(width/div)
    

    def _determine_random_span(self, rand):
        span = 1
        for constraint in self.constraints.get_constraints_for_variable(rand):
            if isinstance(constraint, InnerBlock):
               span = constraint.width
        return span
    
    def _instantiate_random_variables(self, n, rand, plans):
        # NOTE to self: this will only work if there is one random variable :)
        """
        Think about this like instantiating the elements of a matrix of random variables
        """
        assert plans is not None
        width = self._determine_random_width(rand)
        span = self._determine_random_span(rand)
        variables = rand.variables if isinstance(rand, MultiFactVariable) else [rand]

        random_index = self.variables.index(variables[0])
        randomizer = Randomizer(rand, width, span, int(n*self.get_width()/width/span))
        return randomizer.apply_randomization(width, span, random_index, n, plans)
     




    def _generate_random_variables(self, n, variable, width):
        ws_conditions = generate_conditions(n, variable, width)
        return ws_conditions
    
    def get_blocks(self, plan, width, span):
        """Chunk the plan into blocks of size width * span."""
        block_size = width * span
        return [plan[i:i + block_size] for i in range(0, len(plan), block_size)]

    def replace_condition(self, condition_str, replacement, index_to_replace):
        """Replace part of a condition string at the given index."""
        parts = condition_str.split("-")
        parts[index_to_replace] = replacement
        return "-".join(parts)
    
 

    def apply_randomization(self, width, span, random_index, n, plans):
        new_plans = []
        for plan_idx, plan in enumerate(plans):
            blocks = self.get_blocks(plan, width, span)
            reps_per_plan = int(n / len(plans))
            for rep_idx in range(reps_per_plan):
                new_plan = []

                for block_idx, block in enumerate(blocks):
                    # FIXME: does  not work when random variables are the outer design
               
                    rand_idx = rep_idx * len(blocks) + plan_idx * int(n/len(plans)) + block_idx
                    rand_var = self.rand_vars[rand_idx]
                    for cond_idx in range(width):
                        for within_block_idx in range(span):
                            index = cond_idx * span + within_block_idx
                            old_condition = block[index]

                            if isinstance(self.variable, MultiFactVariable):
                                variables = self.variable.variables
                                replacement = rand_var[cond_idx]
                                replacement = replacement.split("-")

                                #FIXME: ugly
                                for i in range(len(variables)):
                                    var_replacement = replacement[i]
                                    new_condition = self.replace_condition(old_condition, var_replacement, random_index+i)
                                    old_condition = new_condition

                            else:
                                replacement = rand_var[cond_idx]
                                new_condition = self.replace_condition(old_condition, replacement, random_index)
                            new_plan.append(new_condition)

                new_plans.append(new_plan)
        return new_plans
    




  