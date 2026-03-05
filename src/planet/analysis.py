from planet.design import Design
from itertools import combinations
from planet.variable import ExperimentVariable, MultiFactVariable

class Analysis:
    """Main class for analyzing experimental designs."""
    def __init__(self, design:Design):

        if design.variables is None:
            raise AttributeError("This design has no variables!")

        self.design = design
        self.main_effects = set()
        self.interaction_effects = set()
        self.time_varying_effects = set()
        self.ws_comparisons = set()

        self.counterbalanced_variables = [
            design_variable
            for design_variable in self.design.design_variables.values()
            if design_variable.is_counterbalanced and not design_variable.is_repeated
        ]

        self.perform_analysis()

    def analyze_main_effects(self):
        """Update main effects based on the design's variables. The main effect
        is estimable if it is a variable in the design and there are more
        than two conditions for that variable. This is under the assumption that
        all plans are distinct and each plan is assigned an equal number of times.
        """

        # main effects are unbiased and estimable if there are more than one
        # conditons assigned to participants for that variable and the number of
        # plans is divisible by the number of conditions for that variable (i.e.
        # the variable conditions are assigned an equal number of times)
        for var in self.design.variables:
            if len(var.conditions) >= 2 and (self.design.num_plans()*self.design.trials % len(var.conditions)) == 0:
                self.main_effects.add(var)
    

    def analyze_interaction_effects(self):
        """Analyze and update interaction effects based on the design's variables.

        An interaction effect is estimable if:
        - all of its component main effects are estimable
        - the number of plans is divisible by the product of the number of
        conditions for each variable in the interaction (i.e., the interaction
        conditions are assigned an equal number of times)
        - the combined main effects appear an equal number of times across all
        assignments. 
        """

        # First, we want to identify all multivariable combinations that are
        # explicitly counterbalanced in the design. 
        # NOTE: need to check properties with rankings.
        # NOTE: we only want pairwise combinations, and we can infer this from
        # interactiosn with three or more variables. This is a TODO. 
        for design_variable in self.counterbalanced_variables:
            if design_variable.is_multifact and len(design_variable.get_variable()) >= 2:
                if (self.design.num_plans()*self.design.trials % len(design_variable) == 0):
                    self.interaction_effects.add(design_variable.get_variable())

       # Then, we want to identify all implicit combinations created by adding
       # individual variables to a design. This occurs when two variables are
       # added independently to a design, and the plan limit is less than the
       # maximum number of plans. 

        # What is the effect of including precomputed plans? I think just
        # redundant computation.
        plan_count, _ = self.design._calculate_maximum_plans()
        plan_limit = self.design.num_groups

        inner_variables = [
            design_var.constraint_spec["InnerBlock"]
            for design_var in self.design.design_variables.values()
            if design_var.is_ranked
        ]

        if (plan_count <= plan_limit or plan_limit == 0):
             # Add every pair of variables as a multifact variable
            for var1, var2 in combinations(self.design.variables, 2):
                var1_dv = self.design.design_variables[var1]
                var2_dv = self.design.design_variables[var2]
                # at least on variable must be unranked 
                if not var1_dv.is_ranked or not var2_dv.is_ranked:
    
                    multifact_var = MultiFactVariable([var1, var2])
                    self.interaction_effects.add(multifact_var)
            
        # Lastly, we want to identify all implicit combinations created by
        # composing designs. 
        # - get all counterbalanced variables with outer block. 
        # - get all variables with inner block. 
        # - For each pair, check if inner block is within the bounds of outer block.
        inner_variables = [
            design_var.constraint_spec["InnerBlock"]
            for design_var in self.design.design_variables.values()
            if design_var.is_blocked_inner
        ]

        outer_variables = [
            design_var.constraint_spec["OuterBlock"]
            for design_var in self.design.design_variables.values()
            if design_var.is_blocked_outer
        ]
        
        # NOTE: this checks for nest! Still need to check for cross ;) 
        for outer_var in outer_variables:
            for inner_var in inner_variables:
                if outer_var.height <= inner_var.height and outer_var.variable != inner_var.variable:
                    interaction = MultiFactVariable([outer_var.variable, inner_var.variable])
                    self.interaction_effects.add(interaction)

        # For cross, need to check that counterbalance is on same width as the
        # inner block, and that the either the number of trials is the same as
        # the number of conditions or there is an outer block with a width the
        # same as the number of conditions! 
       
    def analyze_time_varying_effects(self):
        """Analyze and update time-varying effects based on the design's variables.

        A time-varying effect is estimable if:
        - the primary effect is estimable
        - The variable is counterbalanced (i.e., its conditions are evenly distributed across trials).
        - If the variable is a multifact variable, its sub-variables are also
        time-varying.
        
        Joint-variables (i.e., multifact variables) may not be explicitly
        counterbalanced. In these cases, we can infer counterbalancing if the
        individual variables are counterbalanced and they have overlapping inner
        and outer blocks, respectively. 
        """

        # Analyze time-varying effects
        if self.design.trials > 1 or self.design.trials == 0:
            for counterbalanced_variable in self.counterbalanced_variables:
                self.time_varying_effects.add(counterbalanced_variable.get_variable())

        for var1, var2 in combinations(self.counterbalanced_variables, 2):
            if (self.design.trials > 1 or self.design.trials == 0) and (self.design.num_plans() % (len(var1) * len(var2)) == 0): 
                combined_var = MultiFactVariable([var1.variable, var2.variable])
                if combined_var in self.interaction_effects:
                    self.time_varying_effects.add(combined_var)



    def analyze_ws_comparisons(self):
        """
        Determine whether the variable is compared within-subjects. This is true
        if every participant is exposed to *every* condition of the variable. A
        variable can be added as within-subjects and lack comprehensive
        comparisons if the number of trials is less than the number of
        conditions. 
        """

        for var in self.design.design_variables.values():
            
            no_repeat = var.constraint_spec.get("NoRepeat")
            if no_repeat is None:
                continue  # Skip variables without a NoRepeat constraint

            width = no_repeat.width
            stride = no_repeat.stride

            if width/stride % len(var.variable) == 0:
                self.ws_comparisons.add(var.get_variable())
                self.ws_comparisons.update(var.get_variable().get_variables())

        inner_variables = [
            design_var.constraint_spec["InnerBlock"]
            for design_var in self.design.design_variables.values()
            if design_var.is_blocked_inner and not design_var.is_repeated
        ]

        outer_variables = [
            design_var.constraint_spec["OuterBlock"]
            for design_var in self.design.design_variables.values()
            if design_var.is_blocked_outer and not design_var.is_repeated
        ]
        
        for outer_var in outer_variables:
            for inner_var in inner_variables:
                if outer_var.width <= inner_var.width and self.design.trials % outer_var.width * inner_var.width == 0 and outer_var != inner_var:
             
                    interaction = MultiFactVariable([outer_var.variable, inner_var.variable])
                    self.ws_comparisons.add(interaction)
                    self.ws_comparisons.update(interaction.get_variables())

    def perform_analysis(self):
        self.analyze_main_effects()
        self.analyze_interaction_effects()
        self.analyze_time_varying_effects()
        self.analyze_ws_comparisons()

    def __str__(self):
        return (
            f"Analysis Summary:\n"
            f"- Main Effects: \n\t" + "\n\t".join(str(var) for var in self.main_effects) + "\n"
            f"- Interaction Effects: \n\t" + "\n\t".join(str(var) for var in self.interaction_effects) + "\n"
            f"- Time-Varying Effects: \n\t" + "\n\t".join(str(var) for var in self.time_varying_effects) + "\n"
            f"- Within-Subjects Comparisons: \n\t" + "\n\t".join(str(var) for var in self.ws_comparisons) + "\n"
        )
    

def compare(design1: Design, design2: Design):
    """
    Compares two designs and prints the effects that are testable in one but not the other.
    + indicates effects that are testable in design 1 but not design 2.
    - indicates effects that are testable in design 2 but not design 1.
    """

    analysis1 = Analysis(design1)
    analysis2 = Analysis(design2)

    # Compute differences and intersections
    design1_main_effects = analysis1.main_effects.difference(analysis2.main_effects)
    design2_main_effects = analysis2.main_effects.difference(analysis1.main_effects)
    shared_main_effects = analysis1.main_effects.intersection(analysis2.main_effects)

    design1_interaction_effects = analysis1.interaction_effects.difference(analysis2.interaction_effects)
    design2_interaction_effects = analysis2.interaction_effects.difference(analysis1.interaction_effects)
    shared_interaction_effects = analysis1.interaction_effects.intersection(analysis2.interaction_effects)

    design1_time_varying_effects = analysis1.time_varying_effects.difference(analysis2.time_varying_effects)
    design2_time_varying_effects = analysis2.time_varying_effects.difference(analysis1.time_varying_effects)

    design1_ws_comparisons = analysis1.ws_comparisons.difference(analysis2.ws_comparisons)
    design2_ws_comparisons = analysis2.ws_comparisons.difference(analysis1.ws_comparisons)

    print("Comparative Analysis")
    print("+ indicates effects testable in design 1 but not design 2.")
    print("- indicates effects testable in design 2 but not design 1.\n")

    # Main effects
    print("Main Effects:")
    for var in design1_main_effects:
        print(f"\t+ {var}")
    for var in design2_main_effects:
        print(f"\t- {var}")
    for var in shared_main_effects:
        # Check if the shared main effect is conditional on an interaction effect
        for interaction_var in design1_interaction_effects:
            if var in interaction_var.get_variables():
                print(f"\t+ {var} (under assumption of interaction with {interaction_var})")
        for interaction_var in design2_interaction_effects:
            if var in interaction_var.get_variables():
                print(f"\t- {var} (under assumption of interaction with {interaction_var})")

    # Interaction effects
    print("\nInteraction Effects:")
    for var in design1_interaction_effects:
        print(f"\t+ {var}")
    for var in design2_interaction_effects:
        print(f"\t- {var}")
    # Check if shared interaction effects are conditional on time-varying effects
    for var in shared_interaction_effects:
        if var in design1_time_varying_effects:
            print(f"\t+ {var} (under assumption of time-varying effect of {var})")
        if var in design2_time_varying_effects:
            print(f"\t- {var} (under assumption of time-varying effect of {var})")

    # Time-varying effects
    print("\nTime-Varying Effects:")
    for var in design1_time_varying_effects:
        print(f"\t+ {var}")
    for var in design2_time_varying_effects:
        print(f"\t- {var}")

    # Within-subjects comparisons
    print("\nWithin-Subjects Comparisons:")
    for var in design1_ws_comparisons:
        print(f"\tDesign 1 requires fewer participants than Design 2 to estimate the effect of {var}")
    for var in design2_ws_comparisons:
        print(f"\tDesign 2 requires fewer participants than Design 1 to estimate the effect of {var}")