# External libraries
from z3 import *             
import copy
import math
import pandas as pd

# Planet system imports
from planet.unit import Groups
from planet.variable import  multifact, ExperimentVariable, MultiFactVariable
from planet.design import Design
from planet.constraint import (
    StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock,
    SetRank, SetPosition, AbsoluteRank
)

def eval(designs):
    for design in designs:
        if design.num_plans() == 0:
            design._determine_num_plans()
        
def is_counterbalanced(d1, d2):
    return d1.counterbalanced or d2.counterbalanced

def nest_structure(d1, d2):
    constraints = []
    # Match all variables from the outer design within each block matrix
    
    for variable in d2.design_variables:
        constraints.append(InnerBlock(
            variable,
            d1.get_width(),
            d1.num_plans(),
            stride = [1, 1]
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


def copy_nested_constraints(design1, design2):
    width1, width2 = design1.get_width(), design2.get_width()
    total_groups = design1.num_plans() * design2.num_plans()
    total_conditions = width1 * width2
    constraints = []
    # need to modify the inner constraints region
    # Add counterbalance constraints from design1
    for constraint in design1.constraints.get_constraints():
        if isinstance(constraint, Counterbalance):
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=constraint.width or design1.get_width(),
                    height=constraint.height or design1.num_plans(),
                    stride=constraint.stride
                )
            )

        elif isinstance(constraint, NoRepeat):
            constraints.append(
                NoRepeat(
                    constraint.variable,
                    width=constraint.width if constraint.width < design1.get_width() else design1.get_width(),
                    stride=constraint.stride
                )
            )

        elif isinstance(constraint, InnerBlock):
            
            constraints.append(
                InnerBlock(
                    constraint.variable,
                    width=constraint.width or design1.get_width(),
                    height=constraint.height,
                    stride=constraint.stride
                )
            )

        else:
            constraints.append(copy.copy(constraint))


    # need to modify out constraint region
    for constraint in design2.constraints.get_constraints():
        # FIXME FIXME, I think this is a ratio problem
        if isinstance(constraint, Counterbalance):
            stride = [design1.num_plans(), width1 * constraint.stride[1]]
            # Add counterbalance constraint for design2 variables
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=total_conditions,
                    height=total_groups,
                    stride=stride
                )
            )

        elif isinstance(constraint, NoRepeat):
            width = constraint.width if constraint.width < width2 else width2
            constraints.append(
                NoRepeat(
                    constraint.variable,
                    width*width1,
                    constraint.stride*width1
                )
            )
    
        elif isinstance(constraint, InnerBlock):
            constraints.append(
                InnerBlock(
                    constraint.variable, 
                    constraint.width*width1, 
                    constraint.height*design1.num_plans(), 
                    stride = [1, 1])
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(constraint, OuterBlock):
            constraints.append(
                OuterBlock(
                    constraint.variable, 
                    constraint.width*width1, 
                    constraint.height*design1.num_plans(), 
                    stride = [1, 1])
            )
            
        else:
            constraints.append(copy.copy(constraint))
            
    return constraints


def add_design_variables(*, des, combined_des):
    for v in des.design_variables:
        combined_des.add_variable(v)


def nest(*, outer:Design, inner:Design):
    """
    Nest two designs to create a combined experimental design.

    Args:
        outer: The outer design object.
        inner: The inner design object.

    Returns:
        A new Design object representing the nested experimental design.
    """
    total_groups = inner.num_plans() * outer.num_plans()
    total_conditions = inner.get_width() * outer.get_width()

    combined_design = (
        Design()
        .limit_plans(total_groups)
        .num_trials(total_conditions)
    )


    # NOTE: ORDER MATTERS HERE... The design variable spec stores one outermatch
    # constraint. Prioritze existing constraints, as they will always have a
    # width equal to or smaller. Make this more elegant later?
    # combined_design.add_variables(combined_variables)
    add_design_variables(des = inner, combined_des = combined_design)
    add_design_variables(des = outer, combined_des = combined_design)
    # Nest structural constraints and copy semantic ones
    copied_constraints = copy_nested_constraints(inner, outer)
    if copied_constraints:
        combined_design.add_constraints(copied_constraints)

    combined_design.add_constraints(nest_structure(inner, outer))


    return combined_design




