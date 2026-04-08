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
            if design_variable.is_counterbalanced or design_variable.is_random
        ]

        self.perform_analysis()


    def analyze_main_effects(self):
        """Update main effects based on the design's variables. The main effect
        is estimable if it is a variable in the design and there are more
        than two conditions for that variable. This is under the assumption that
        all plans are distinct and each plan is assigned an equal number of times.
        """
    
        for var, dvar in self.design.design_variables.items():
            if dvar.is_counterbalanced or dvar.is_random: 
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
            
            if dvar.is_counterbalanced or dvar.is_random:
                if len(var.conditions) >= 2:
                    if var.is_multifact():
                        # Add new multifact variables for all pairs of constituent variables
                        constituent_vars = var.get_variables()  # or however you access the component variables
                        for v1, v2 in combinations(constituent_vars, 2):
                            pair_var = MultiFactVariable([v1, v2])  # replace with your actual constructor
                            self.interaction_effects.add(pair_var)
            elif not dvar.is_repeated and dvar.is_ordered:
                if len(var.conditions) >= 2:
                    if var.is_multifact():
                        # Add new multifact variables for all pairs of constituent variables
                        constituent_vars = var.get_variables()  # or however you access the component variables
                        for v1, v2 in combinations(constituent_vars, 2):
                            pair_var = MultiFactVariable([v1, v2])  # replace with your actual constructor
                            self.interaction_effects.add(pair_var)
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
            if (var1_dv.is_counterbalanced or var1_dv.is_random) and (var2_dv.is_counterbalanced or var2_dv.is_random):
                if (plan_count <= plan_limit or plan_limit == 0):
                    multifact_var = MultiFactVariable([var1, var2])
                    self.interaction_effects.add(multifact_var)

            elif ((var1_dv.is_counterbalanced or var1_dv.is_random) and var2_dv.is_ordered) or ((var2_dv.is_counterbalanced or var2_dv.is_random) and var1_dv.is_ordered):
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

                    if (outer_spec.width <= inner_spec.width and inner_spec.height <= outer_spec.height) and (outer_check or (outer_var.is_counterbalanced or outer_var.is_random)) and (inner_check or (inner_var.is_counterbalanced or inner_var.is_random)): 
                        interaction = MultiFactVariable([outer_var.variable, inner_var.variable])
                        self.interaction_effects.add(interaction)

                    elif (inner_spec.height <= outer_spec.height) and (outer_check or (outer_var.is_counterbalanced or outer_var.is_random)) and (inner_var.is_counterbalanced or inner_var.is_random):
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
        # if self.design.get_width() > 1:
        for counterbalanced_variable in self.counterbalanced_variables:
            if counterbalanced_variable.get_variable().is_multifact(): 
                self.time_varying_effects.update(counterbalanced_variable.get_variable().get_variables())
                subvars = counterbalanced_variable.get_variable().get_variables()
                self.time_varying_effects.update(subvars)
                for var_a, var_b in combinations(subvars, 2):
                    self.time_varying_effects.add(MultiFactVariable([var_a, var_b]))
            else: 
                self.time_varying_effects.add(counterbalanced_variable.get_variable())
                

        for var1, var2 in combinations(self.counterbalanced_variables, 2):
            # if (self.design.get_width() > 1): 
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

            if (width/stride) % len(var.variable) == 0 and self.design.get_width() % len(var.variable) == 0:
                subvars = var.get_variable().get_variables()
                self.ws_comparisons.update(subvars)
                for var_a, var_b in combinations(subvars, 2):
                    self.ws_comparisons.add(MultiFactVariable([var_a, var_b]))
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

        if any(dvar.is_random for dvar in self.design.design_variables.values()):
            str = "There are random variables in this design, which means that the analysis is subject to random variation and is more likely to hold in larger samples. Consider adding counterbalancing constraints to ensure that the analysis holds in smaller samples.\nVariables that are completely randomized:\n"


            for var, dvar in self.design.design_variables.items():
                if dvar.is_random:
                    for var in var.get_variables():
                        str += f"\t{var}\n"

            warnings.warn(str)

        


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

    def diff_sets(a, b):
        return a.difference(b), b.difference(a), a.intersection(b)

    def print_diff(d1_only, d2_only):
        for var in d1_only:
            print(f"\t+ {var}")
        for var in d2_only:
            print(f"\t- {var}")

    main1, main2, shared_main           = diff_sets(analysis1.main_effects, analysis2.main_effects)
    inter1, inter2, shared_inter        = diff_sets(analysis1.interaction_effects, analysis2.interaction_effects)
    time1, time2, _                     = diff_sets(analysis1.time_varying_effects, analysis2.time_varying_effects)
    ws1, ws2, shared_ws                 = diff_sets(analysis1.ws_comparisons, analysis2.ws_comparisons)

    print("Comparative Analysis")
    print("+ indicates effects testable in design 1 but not design 2.")
    print("- indicates effects testable in design 2 but not design 1.\n")

    # Main effects
    print("Main Effects:")
    print_diff(main1, main2)

    for var in shared_main:
        for sign, interaction_vars, time_vars in [("+", inter1, time1), ("-", inter2, time2)]:
            for interaction_var in interaction_vars:
                if var in interaction_var.get_variables():
                    print(f"\t{sign} {var} (under assumption of interaction with {interaction_var})")
            for time_var in time_vars:
                if not time_var.is_multifact() and var in time_var.get_variables():
                    print(f"\t{sign} {var} (under weaker assumption of no time-varying effect)")

    # Interaction effects
    print("\nInteraction Effects:")
    print_diff(inter1, inter2)

     
    for var in shared_inter:
        if var in time1:
            print(f"\t+ {var} (under weaker assumption of no time-varying effect of {var})")
        if var in time2:
            print(f"\t- {var} (under weaker assumption of no time-varying effect of {var})")

    # Time-varying effects
    print("\nTime-Varying Effects:")
    print_diff(time1, time2)

    # Within-subjects comparisons
    print("\nWithin-Subjects Comparisons:")
    print_diff(ws1, ws2)

    width_diff = design1.get_width() - design2.get_width()
    if width_diff != 0:
        wider, narrower = ("Design 1", "Design 2") if width_diff > 0 else ("Design 2", "Design 1")
        for var in shared_ws:
            print(f"\t{wider} requires fewer participants than {narrower} to estimate the effect of {var}")