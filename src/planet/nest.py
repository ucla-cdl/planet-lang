# External libraries
from z3 import *                 # Requires: pip install z3-solver
import copy
import math
import pandas as pd

# Planet system imports
from planet.unit import Groups
from planet.variable import  multifact, ExperimentVariable
from planet.replications import Replications
from planet.design import Design, RandomPlan, Plans
from planet.constraint import (
    StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock,
    SetRank, SetPosition, AbsoluteRank
)
from planet.designer import Designer
from planet.candl import combine_lists
# from planet.helpers import (
#     build_matrix, some_helper_function  # ← Replace with actual names
# )
# from planet.narray import (
#     make_array, flatten_array  # ← Replace with actual functions you use
# )


def eval(designs):
    for design in designs:
        if design.groups is None:
            design._determine_num_plans()
        
        


def is_counterbalanced(d1, d2):
    return d1.counterbalanced or d2.counterbalanced

def nest_structure(d1, d2):
    constraints = []
    # Match all variables from the outer design within each block matrix
    
    for i in range(len(d2.variables)):
        constraints.append(InnerBlock(
            d2.variables[i],
            d1.get_width(),
            len(d1.groups),
            stride = [1, 1]
        ))

     # Match all variables from the inner design across every block

    for i in range(len(d1.variables)):
        constraints.append(OuterBlock(
            d1.variables[i],
            d1.get_width(),
            len(d1.groups),
            stride = [1, 1]
        ))

 
    return constraints


def copy_nested_constraints(design1, design2):
    width1, width2 = design1.get_width(), design2.get_width()
    total_groups, total_conditions = len(design1.groups) * len(design2.groups), width2 * width1
    constraints = []
    total_conditions = width2 * width1
    constraints = []
    # need to modify the inner constraints region
    # Add counterbalance constraints from design1
    for constraint in design1.constraints:
        if isinstance(constraint, Counterbalance):
            width = constraint.width or design1.get_width()
            height = constraint.height or len(design1.groups)
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=width,
                    height=height,
                    stride=constraint.stride
                )
            )
        elif isinstance(constraint, NoRepeat):
  
            constraints.append(
                NoRepeat(
                    constraint.variable,
                    width=width1,
                    stride=constraint.stride
                )
            )
        else:
            constraints.append(copy.copy(constraint))


    # need to modify out constraint region
    for constraint in design2.constraints:
        # FIXME FIXME, I think this is a ratio problem
        if isinstance(constraint, Counterbalance):
            
            # Add counterbalance constraint for design2 variables
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=total_conditions,
                    height=total_groups,
                    stride=[len(design1.groups), width1*constraint.stride[1]]
                )
            )

        if isinstance(constraint, StartWith):
                constraints.append(
                    copy.copy(constraint)
                )
        elif isinstance(constraint, AbsoluteRank):
                constraints.append(
                    copy.copy(constraint)
                )

        elif isinstance(constraint, SetRank):
                constraints.append(
                    copy.copy(constraint)
                )

        elif isinstance(constraint, SetPosition):
                constraints.append(
                    copy.copy(constraint)
                )
        
        elif isinstance(constraint, NoRepeat):
            constraints.append(
                NoRepeat(
                    constraint.variable,
                    constraint.width*width1,
                    constraint.stride*width1
                )
            )
    
        if isinstance(constraint, InnerBlock):
            constraints.append(
                InnerBlock(
                    constraint.variable, 
                    constraint.width*width1, 
                    constraint.height*len(design1.groups), 
                    stride = [1, 1])
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(constraint, OuterBlock):
            constraints.append(
                OuterBlock(
                    constraint.variable, 
                    constraint.width*width1, 
                    constraint.height*len(design1.groups), 
                    stride = [1, 1])
            )

    return constraints


def can_nest(d1, d2):
    if isinstance(d1, Plans) and isinstance(d2, Plans):
        return True
    
class RandomDesignError(Exception):
    pass

def handle_empty_design(des):
    des = copy.copy(des)
    if des.is_empty:
        var = ExperimentVariable("base", 1)
        des._add_variable(var)
        des.groups = Groups(1)
        des.constraints.append(Counterbalance(var, width = des.trials, height = 1, stride = [1,1]))
    return des

def nest(*, outer, inner):
    """
    Nest two designs together to create a combined experimental design.
    
    Args:
        design1: First design object
        design2: Second design object
        
    Returns:
        Combined design object
    """

    # possibly FIXME?
    outer = handle_empty_design(outer)
    inner = handle_empty_design(inner)
    
    
    # FIXME: problem with norepeat when recursive nest and nested design is
    # outer design of a new nested design

    # first, check if one design is random
    # if so, conver to a special replications type.
    if (not isinstance(inner, Replications)) and (inner.has_random_variable() or inner.is_random()):
        inner = RandomPlan(inner.variables).num_trials(inner.get_width())

    elif (not isinstance(outer, Replications)) and (outer.has_random_variable() or outer.is_random()):
        outer = RandomPlan(outer.variables)

    assert can_nest(outer, inner)

    eval([inner, outer])
    # FIXME: ugly
    num_groups = len(outer.groups)
    if not len(outer.groups):
        outer.eval()
        num_groups = len(outer.plans)
    # Calculate the total number of groups in the combined design
    total_groups = len(inner.groups) * num_groups

    # Combine variables from both designs
    combined_variables = combine_lists(inner.variables, outer.variables)
    
    # Calculate width1 (the product of all variable lengths in design1)
    width1 = inner.get_width()
    width2 = outer.get_width()
    total_conditions = width2 * width1
 
    # Create a new design with the combined variables
    combined_design = (Design()
                    #    .within_subjects(multifact(combined_variables))
                       .limit_groups(total_groups)
                       .num_trials(total_conditions)
                    )


    # FIXME
    combined_design._add_variable(multifact(combined_variables))

    combined_design.random_var.extend(inner.random_var)
    combined_design.random_var.extend(outer.random_var)
    combined_design.constraints.extend(nest_structure(inner, outer))

    inner_constraints = copy_nested_constraints(inner, outer)
    if inner_constraints is not None:
        combined_design.constraints.extend(inner_constraints)
    
    
 
    return combined_design




def cross_structure(d1, d2):
    constraints = []
    # Match all variables from the outer design within each block matrix
    
    for i in range(len(d2.variables)):
        print(d2.variables[i])
        constraints.append(InnerBlock(
            d2.variables[i],
            1,
            len(d1.groups),
            stride = [1, 1]
        ))

     # Match all variables from the inner design across every block

    for i in range(len(d1.variables)):
        constraints.append(OuterBlock(
            d1.variables[i],
            d1.get_width(),
            len(d1.groups),
            stride = [1, 1]
        ))

 
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

    # first, check if one design is random
    # if so, conver to a special replications type.
    if (not isinstance(design1, Replications)) and (design1.has_random_variable() or design1.is_random()):
        design1 = RandomPlan(design1.variables).num_trials(design1.get_width())

    elif (not isinstance(design2, Replications)) and (design2.has_random_variable() or design2.is_random()):
        design2 = RandomPlan(design2.variables)

    eval([design1, design2])

    # Calculate the total number of groups in the combined design
    total_groups = len(design1.groups) * len(design2.groups)
    print(len(design2.groups))
    # Combine variables from both designs
    combined_variables = combine_lists(design1.variables, design2.variables)
    
    # Calculate width1 (the product of all variable lengths in design1)
    width1 = design1.get_width()
    width2 = design2.get_width()
    
    assert width1 == width2
    total_conditions = width2 

    
    # Create a new design with the combined variables
    combined_design = ( Design()
                       .within_subjects(multifact(combined_variables))
                       .limit_groups(total_groups)
                       .num_trials(total_conditions)
                    )
   
   
    # need to modify the inner constraints region
    # Add counterbalance constraints from design1
    for constraint in design1.constraints:
        if isinstance(constraint, Counterbalance):
            if constraint.width and constraint.height:
                combined_design.constraints.append(
                    Counterbalance(
                        constraint.variable,
                        width=constraint.width,
                        height=constraint.height,
                        stride=constraint.stride
                    )
                )
            else: 
                combined_design.constraints.append(
                    Counterbalance(
                        constraint.variable,
                        width=width1,
                        height=len(design1.groups),
                        stride=constraint.stride
                    )
                )

        
        elif isinstance(constraint, NoRepeat):
            combined_design.constraints.append(
                NoRepeat(
                    constraint.variable,
                    constraint.width,
                    constraint.stride
                )
            )

        elif isinstance(constraint, AbsoluteRank):
                combined_design.constraints.append(
                    copy.copy(constraint)
                )

        elif isinstance(constraint, InnerBlock):
            combined_design.constraints.append(
                InnerBlock(constraint.variable, constraint.width, constraint.height, stride = [1, 1])
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(constraint, OuterBlock):
            combined_design.constraints.append(
                OuterBlock(constraint.variable, constraint.width, constraint.height, stride = [1, 1])
            )

    
    # need to modify out constraint region
    for constraint in design2.constraints:
        if isinstance(constraint, Counterbalance):
            stride_height = constraint.height if constraint.height else len(design1.groups)
            
            # Add counterbalance constraint for design2 variables
            combined_design.constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=total_conditions,
                    height=total_groups,
                    stride=[stride_height, 1]
                )
            )

        elif isinstance(constraint, StartWith):
                combined_design.constraints.append(
                    StartWith(constraint.variable, constraint.condition)
                )
        
        elif isinstance(constraint, AbsoluteRank):
                combined_design.constraints.append(
                    copy.copy(constraint)
                )
        
        elif isinstance(constraint, NoRepeat):
        
              combined_design.constraints.append(
                NoRepeat(
                    constraint.variable,
                    constraint.width,
                    constraint.stride
                )
            )
    
        elif isinstance(constraint, InnerBlock):
            stride_height = constraint.height if constraint.height else len(design1.groups)
            combined_design.constraints.append(
                InnerBlock(constraint.variable, constraint.width,constraint.height*len(design1.groups), stride = [1, 1])
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(constraint, OuterBlock):
            stride_height = constraint.height if constraint.height else len(design1.groups)
            combined_design.constraints.append(
                OuterBlock(constraint.variable, constraint.width, constraint.height*len(design1.groups), stride = [stride_height, 1])
            )

    combined_design.constraints.extend(cross_structure(design1, design2))
    combined_design.random_var.extend(design1.random_var)
    combined_design.random_var.extend(design2.random_var)
    
    return combined_design