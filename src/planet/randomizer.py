from planet.candl import generate_conditions
from planet.constraint import InnerBlock, OuterBlock



class Randomizer:
    def __init__(self, variable, width, span, random_index, n, participants, plans):
        rand_vars = self._generate_random_variables(n, variable, width)
        self.randomized_plans = self._apply_randomization(rand_vars, width, span, random_index, participants, plans)
      
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

    def _apply_randomization(self, rand_vars, width, span, random_index, n, plans):
        new_plans = []

      
        for plan_idx, plan in enumerate(plans):
            blocks = self.get_blocks(plan, width, span)
            reps_per_plan = int(n / len(plans))

            for rep_idx in range(reps_per_plan):
                new_plan = []

                for block_idx, block in enumerate(blocks):
                    # FIXME: does  not work when random variables are the outer design
                    rand_idx = rep_idx * len(blocks) + plan_idx * int(n/len(plans)) + block_idx
                    rand_var = rand_vars[rand_idx]
                    for cond_idx in range(width):
                        for within_block_idx in range(span):
                            index = cond_idx * span + within_block_idx
                            old_condition = block[index]
                            replacement = rand_var[cond_idx]
                            new_condition = self.replace_condition(old_condition, replacement, random_index)
                            new_plan.append(new_condition)

                new_plans.append(new_plan)

        return new_plans
    
    def get_plans(self):
        return self.randomized_plans




  