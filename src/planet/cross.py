# External libraries
from z3 import *             
import copy
from planet.design import Design
from planet.constraint import (
    StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock,
    SetRank, SetPosition, AbsoluteRank
)
from planet.candl import combine_lists
from planet.region import DesignRegion


def cross_structure(d1, d2):
    constraints = []
    # Match all variables from the outer design within each block matrix
    for variable in d2.design_variables:
        constraints.append(InnerBlock(
            variable,
            DesignRegion(1, d1.num_plans(), [1, 1])
        ))

     # Match all variables from the inner design across every block
    for variable in d1.design_variables:
        constraints.append(OuterBlock(
            variable,
            d1.get_width(),
            d1.num_plans(),
            stride = [1, 1]
        ))
    return constraints


def copy_crossed_constraints(design1, design2, total_conditions, total_groups):
    constraints = []
     # need to modify the inner constraints region
    # Add counterbalance constraints from design1
    for constraint in design1.constraints.constraints:
        if isinstance(constraint, Counterbalance):
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=constraint.width or design1.get_width(),
                    height=constraint.height or design1.num_plans(),
                    stride=constraint.stride
                )
            )

        else:
            constraints.append(
                    copy.copy(constraint)
                )

    # need to modify out constraint region
    for constraint in design2.constraints.constraints:
        if isinstance(constraint, Counterbalance):
            # Each plan of design2 fills design1.num_plans() rows, so its
            # region keeps its shape and takes its rows that far apart.
            rows = design1.num_plans()
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=constraint.width or total_conditions,
                    height=constraint.height * rows if constraint.height else total_groups,
                    stride=[constraint.stride[0] * rows, constraint.stride[1]]
                )
            )
    
        elif isinstance(constraint, InnerBlock):
            stride_height = constraint.height if constraint.height else design1.num_plans()
            constraints.append(
                InnerBlock(constraint.variable, DesignRegion(constraint.width,constraint.height*design1.num_plans(), [1, 1]))
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(constraint, OuterBlock):
            stride_height = constraint.height if constraint.height else design1.num_plans()
            constraints.append(
                OuterBlock(constraint.variable, constraint.width, constraint.height*design1.num_plans(), stride = [stride_height, 1])
            )

        else:
            constraints.append(
                    copy.copy(constraint)
                )

    return constraints



# NOTE: this is an absolute mess :(
# FIXME: come back to this. Won't generalize...
# need to fix how the match blocks work, but this is not a priority
def cross(design1, design2):
    """
    Nest two designs together to create a combined experimental design.
    
    Args:
        design1: First design object
        design2: Second design object
        
    Returns:
        Combined design object
    """

    design1.check_trials()
    design2.check_trials()

    # Calculate the total number of groups in the combined design
    total_groups = design1.num_plans() * design2.num_plans()
    # Combine variables from both designs
    combined_variables = combine_lists(design1.variables, design2.variables)
    # Calculate width1 (the product of all variable lengths in design1)
    width1 = design1.get_width()
    width2 = design2.get_width()
    
    # Raise an error if widths are not equal
    if width1 != width2:
        def is_between_subjects(design):
            # A design is between-subjects if every variable is repeated across
            # trials (no NoRepeat) and blocked at the inner level.
            return all(
                dv.is_repeated and dv.is_blocked_inner
                for dv in design.design_variables.values()
            )

        for narrow, narrow_width in ((design1, width1), (design2, width2)):
            if narrow_width == 1 and is_between_subjects(narrow):
                raise ValueError(
                    "Cannot cross a between-subjects design (width 1) with a "
                    "within-subjects design. A between-subjects factor is not "
                    "crossed; it partitions participants into groups, yielding a "
                    "mixed design. Add the between-subjects factor to your design "
                    "directly instead of crossing, e.g.:\n"
                    "    Design().within_subjects(A).counterbalance(A).between_subjects(B)"
                )

        raise ValueError(
            f"Widths of design1 ({width1}) and design2 ({width2}) are not equal, "
            "so the designs cannot be crossed. Crossing requires both designs to "
            "have the same number of within-subjects conditions (width). Check the "
            "counterbalance/order/within-subjects factors on each design."
        )


    total_conditions = width2 
    
    # Create a new design with the combined variables
    combined_design = ( Design()
                       .limit_plans(total_groups)
                       .num_trials(total_conditions)
                    )
    
    
    
    combined_design.variables.extend(combined_variables)
    combined_design.add_constraints(copy_crossed_constraints(design1, design2, total_conditions, total_groups))
    combined_design.add_constraints(cross_structure(design1, design2))
    combined_design.composition = ('cross', design1, design2)
    combined_design.set_minimum_trials(design1.get_width())

    return combined_design
