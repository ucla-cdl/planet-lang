# External libraries
from z3 import *             
import copy
from planet.design import Design
from planet.constraint import (
    StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock,
    SetRank, SetPosition, AbsoluteRank
)
from planet.candl import combine_lists


def cross_structure(d1, d2):
    constraints = []
    # Match all variables from the outer design within each block matrix
    for i in range(len(d2.variables)):
        constraints.append(InnerBlock(
            d2.variables[i],
            1,
            d1.num_plans(),
            stride = [1, 1]
        ))

     # Match all variables from the inner design across every block

    for i in range(len(d1.variables)):
        constraints.append(OuterBlock(
            d1.variables[i],
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
            if constraint.width and constraint.height:
                constraints.append(
                    Counterbalance(
                        constraint.variable,
                        width=constraint.width,
                        height=constraint.height,
                        stride=constraint.stride
                    )
                )
            else: 
                constraints.append(
                    Counterbalance(
                        constraint.variable,
                        width=design1.get_width(),
                        height=design1.num_plans(),
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
            stride_height = constraint.height if constraint.height else design1.num_plans()
            # Add counterbalance constraint for design2 variables
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=total_conditions,
                    height=total_groups,
                    stride=[stride_height, 1]
                )
            )
    
        elif isinstance(constraint, InnerBlock):
            stride_height = constraint.height if constraint.height else design1.num_plans()
            constraints.append(
                InnerBlock(constraint.variable, constraint.width,constraint.height*design1.num_plans(), stride = [1, 1])
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

 
    # Calculate the total number of groups in the combined design
    total_groups = design1.num_plans() * design2.num_plans()
    # Combine variables from both designs
    combined_variables = combine_lists(design1.variables, design2.variables)
    # Calculate width1 (the product of all variable lengths in design1)
    width1 = design1.get_width()
    width2 = design2.get_width()
    
    assert width1 == width2
    total_conditions = width2 
    
    # Create a new design with the combined variables
    combined_design = ( Design()
                       .limit_plans(total_groups)
                       .num_trials(total_conditions)
                    )
    
    combined_design.variables.extend(combined_variables)
    combined_design.add_constraints(copy_crossed_constraints(design1, design2, total_conditions, total_groups))
    combined_design.add_constraints(cross_structure(design1, design2))
    
    return combined_design