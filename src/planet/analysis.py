from planet.design import Design
from itertools import combinations
from planet.variable import ExperimentVariable, MultiFactVariable
import warnings

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
            if design_variable.is_counterbalanced
        ]

        self.perform_analysis()

    def analyze_main_effects(self):
        """Update main effects based on the design's variables. The main effect
        is estimable if it is a variable in the design and there are more
        than two conditions for that variable. This is under the assumption that
        all plans are distinct and each plan is assigned an equal number of times.
        """
    
        for var, dvar in self.design.design_variables.items():
            if dvar.is_counterbalanced: 
                if len(var.conditions) >= 2:
                    self.main_effects.update(var.get_variables())
            elif not dvar.is_repeated and dvar.is_ordered:
                if len(var.conditions) >= 2:
                    self.main_effects.update(var.get_variables())
            else:
                warnings.warn(f"Could not perform analysis for variable {var}.")
    

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
        for var, dvar in self.design.design_variables.items():
            if var.is_multifact():
                if dvar.is_counterbalanced: 
                    if len(var.conditions) >= 2:
                        self.interaction_effects.add(var)
                elif not dvar.is_repeated and dvar.is_ordered:
                    if len(var.conditions) >= 2:
                        self.interaction_effects.add(var)
                else:
                    warnings.warn(f"Could not perform analysis for variable {var}.")

       # Then, we want to identify all implicit combinations created by adding
       # individual variables to a design. This occurs when two variables are
       # added independently to a design, and the plan limit is less than the
       # maximum number of plans. 

        # What is the effect of including precomputed plans? I think just
        # redundant computation.
        plan_count, _ = self.design._calculate_maximum_plans()
        plan_limit = self.design.num_groups

            # Add every pair of variables as a multifact variable
        for var1, var2 in combinations(self.design.design_variables, 2):
            var1_dv = self.design.design_variables[var1]
            var2_dv = self.design.design_variables[var2]
            # at least on variable must be unranked 
            if var1_dv.is_counterbalanced and var2_dv.is_counterbalanced:
                if (plan_count <= plan_limit or plan_limit == 0):
                    multifact_var = MultiFactVariable([var1, var2])
                    self.interaction_effects.add(multifact_var)

            elif (var1_dv.is_counterbalanced and var2_dv.is_ordered) or (var2_dv.is_counterbalanced and var1_dv.is_ordered):
                multifact_var = MultiFactVariable([var1, var2])
                self.interaction_effects.add(multifact_var)
            
        # Lastly, we want to identify all implicit combinations created by
        # composing designs. 
        # - get all counterbalanced variables with outer block. 
        # - get all variables with inner block. 
        # - For each pair, check if inner block is within the bounds of outer block.
        inner_variables = [
            (design_var, design_var.constraint_spec["InnerBlock"])
            for design_var in self.design.design_variables.values()
            if design_var.is_blocked_inner
        ]

        outer_variables = [
            (design_var, design_var.constraint_spec["OuterBlock"])
            for design_var in self.design.design_variables.values()
            if design_var.is_blocked_outer
        ]
 
        # NOTE: this checks for nest! Still need to check for cross ;) 
        for outer_var, outer_spec in outer_variables:
            for inner_var, inner_spec in inner_variables:
                # the inner block height is always a multiple or factor of the
                # outer block height based on how we compose designs. We always
                # add an inner block when we add an outer block. 
                if (
                    (outer_spec.height <= inner_spec.height 
                    and outer_spec.variable != inner_spec.variable) 
                ):

                    outer_repeats = outer_var.constraint_spec["NoRepeat"]
                    inner_repeats = outer_var.constraint_spec["NoRepeat"]
                

                    outer_check = (
                        ((outer_repeats is not None and 
                        outer_repeats.width*outer_repeats.stride < outer_spec.width and outer_var.is_ordered) and self.design.num_trials > outer_spec.width*outer_spec*outer_spec.stride)
                    ) 

                    inner_check = (
                          ((inner_repeats is not None and 
                        inner_repeats.width*inner_repeats.stride < inner_spec.width and inner_var.is_ordered) and self.design.num_trials > inner_spec.width*inner_spec*inner_spec.stride)
                    ) 

                    if (outer_spec.width <= inner_spec.width and inner_spec.height <= outer_spec.height) and (outer_check or outer_var.is_counterbalanced) and (inner_check or inner_var.is_counterbalanced): 
                        interaction = MultiFactVariable([outer_var.variable, inner_var.variable])
                        self.interaction_effects.add(interaction)

                    elif (inner_spec.height <= outer_spec.height) and (outer_check or outer_var.is_counterbalanced) and inner_var.is_counterbalanced:
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
                if counterbalanced_variable.get_variable().is_multifact(): 
                    self.time_varying_effects.update(counterbalanced_variable.get_variable().get_variables())

        for var1, var2 in combinations(self.counterbalanced_variables, 2):
            if (self.design.trials > 1 or self.design.trials == 0): 
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

        if self.design.is_random:
            warnings.warn("Analysis is not supported for designs with fully random variables. Skipping analysis.")
            return

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

        for time_var in design1_time_varying_effects:
            if not time_var.is_multifact() and var in time_var.get_variables():
                print(f"\t+ {var} (under weaker assumption of no time-varying effect)")

        for time_var in design2_time_varying_effects:
            if not time_var.is_multifact() and var in time_var.get_variables():
                print(f"\t- {var} (under weaker assumption of no time-varying effect)")

    # Interaction effects
    print("\nInteraction Effects:")
    for var in design1_interaction_effects:
        print(f"\t+ {var}")
    for var in design2_interaction_effects:
        print(f"\t- {var}")
    # Check if shared interaction effects are conditional on time-varying effects
    for var in shared_interaction_effects:
        if var in design1_time_varying_effects:
            print(f"\t+ {var} (under weaker assumption of no time-varying effect of {var})")
        if var in design2_time_varying_effects:
            print(f"\t- {var} (under weaker assumption of no time-varying effect of {var})")

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