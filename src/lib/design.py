from z3 import *
from lib.unit import Groups
from lib.orders import Sequence
from lib.candl import *
from lib.variable import MultiFactVariable, multifact
from .helpers import *
from .narray import *
from .candl import *
from .unit import Groups
import copy
from lib.constraint import StartWith, Counterbalance, NoRepeat, InnerBlock, OuterBlock, Constraint
from lib.designer import Designer
from lib.candl import generate_conditions
import math
import pandas as pd

class Design:
    """Main class for creating experimental designs."""
    def __init__(self):
        self.sequence = None
        self.variables = []

        self.ws_variables = []
        self.bs_variables = []

        self.groups = None
        self.constraints = []
        self.trials = 0
        
        self.designer = Designer()
        self.counterbalanced = False

        self.plans = None
  
    def to_latex(self):
        matrix = self.eval()
        trials = [f"trial{i+1}" for i in range(len(matrix[0]))]
        df = pd.DataFrame(matrix, columns=trials)

        try:
            filepath = "../outputs/design.tex"
            create_directory_for_file(filepath)
            with open(filepath, 'w', encoding='utf-8') as tex_file:
                tex_file.write(df.to_latex())
            print(f"success")
        except Exception as e:
            print(f"An error occurred: {e}")

    def num_trials(self, n):
        self.trials = n
        return self
    
    def add_variable(self, variable, l):
        assert isinstance(variable, ExperimentVariable)

        if isinstance(variable, MultiFactVariable):
            variables = variable.variables
        else:
            variables = [variable]

        self.variables.extend(variables)
        l.extend(variables)
    
    def between_subjects(self, variable):
        self.add_variable(variable, self.bs_variables)
        return self

    def within_subjects(self, variable):
        self.add_variable(variable, self.ws_variables)
        return self
    
    def limit_groups(self, n):
        self.groups = Groups(n)
        return self
    
    def get_plans(self, n=None):
        if self.plans is not None:
            return self.plans
        return self.eval() if self.counterbalanced else self.random(n or len(self.groups))
    
    def get_width(self):
        return self.trials or math.prod(v.n for v in self.ws_variables)
    
    def start_with(self, variable, condition):
        assert isinstance(variable, ExperimentVariable)
        self.constraints.append(StartWith(variable, condition))
        return self

    # FIXME
    def eval(self, test = False):
        
        """
        Evaluate the experimental design and generate a solution.
        
        Returns:
            The evaluation result from the Assignment solver
        """

        # Get the width of the design
        width = self.get_width()
        sequence = Sequence(width)
        self.groups = self.groups or Groups(0)
        
        self.designer.start(
            self.groups, 
            sequence, 
            self.variables
        )

        # Handle between-subjects constraints
        for variable in self.bs_variables:
            self.constraints.append(
                InnerBlock(
                    variable,
                    width,
                    1
                )
            )
          
        self.designer.solver.all_different()
        self.designer.eval_constraints(self.constraints, self.groups, width)

        if test:
            self.plans = self.designer.eval_all()
        else:
            self.plans = self.designer.eval()

        return self.plans
        
    def counterbalance(self, variable, w = 0, h = 0, stride = [1, 1]):
        assert isinstance(variable, ExperimentVariable)

        self.counterbalanced = True

        if isinstance(variable, MultiFactVariable):
            variable = variable.variables
        else: 
            variable = [variable]

        width = 1
        for v in variable: 
            width *= len(v)

        # FIXME: should probably decouble this constraint block concept?
        self.constraints.append(NoRepeat([variable], width=width))
        self.constraints.append(Counterbalance(variable, width = w, height = h, stride = stride))
        return self
    
    def random(self, n):
        assert len(self.ws_variables) > 0 or len(self.bs_variables) > 0

        ws_variable = None
        bs_variable = None
        bs_conditions = None
        ws_conditions = None
        if len(self.ws_variables) > 0:
            ws_variable = self.ws_variables[0] if len(self.ws_variables) == 1 else multifact(self.ws_variables)
            ws_conditions = generate_conditions(n, ws_variable.conditions,self.get_width())
        if len(self.bs_variables) > 0:
            bs_variable = self.bs_variables[0] if len(self.bs_variables) == 1 else multifact(self.bs_variables)
            bs_conditions = generate_conditions(n, bs_variable.conditions,1)

        conditions = []
        if len(self.bs_variables) > 0 and len(self.ws_variables) > 0:
            for i in range(len(bs_conditions)):
                conditions.append([bs_conditions[i][0] + "-" + ws_conditions[i][j] for j in range(len(ws_conditions[0]))])
        elif len(self.bs_variables) > 0:
            conditions = bs_conditions
        elif len(self.ws_variables) > 0:
            conditions = ws_conditions
        else:
            print("err")
            
        return conditions

def eval(designs):
    for design in designs:
        if design.groups is None:
            design.eval()


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
            if not constraint.width or not constraint.height:
                constraints.append(
                    Counterbalance(
                        constraint.variable,
                        width=design1.get_width(),
                        height=len(design1.groups),
                        stride=constraint.stride
                    )
                )
        else:
            constraints.append(
                copy.copy(constraint)
            )


    # need to modify out constraint region
    for constraint in design2.constraints:
        if isinstance(constraint, Counterbalance):
            # Add counterbalance constraint for design2 variables
            constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=total_conditions,
                    height=total_groups,
                    stride=[width1*constraint.stride[0], len(design1.groups)*constraint.stride[1]]
                )
            )

        elif isinstance(constraint, StartWith):
                constraints.append(
                    copy.copy(constraint)
                )
        
        elif isinstance(constraint, NoRepeat):
              constraints.append(
                NoRepeat(
                    constraint.variable,
                    total_conditions,
                    width1*constraint.stride
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


def nest(design1, design2):
    """
    Nest two designs together to create a combined experimental design.
    
    Args:
        design1: First design object
        design2: Second design object
        
    Returns:
        Combined design object
    """

    eval([design1, design2])

    # Calculate the total number of groups in the combined design
    total_groups = len(design1.groups) * len(design2.groups)
    # Combine variables from both designs
    combined_variables = combine_lists(design1.variables, design2.variables)
    
    # Calculate width1 (the product of all variable lengths in design1)
    width1 = design1.get_width()
    width2 = design2.get_width()
    total_conditions = width2 * width1
    
    # Create a new design with the combined variables
    combined_design = ( Design()
                       .within_subjects(multifact(combined_variables))
                       .limit_groups(total_groups)
                       .num_trials(total_conditions)
                    )
    
    combined_design.counterbalanced = is_counterbalanced(design1, design2)
    combined_design.constraints.extend(nest_structure(design1, design2))
    combined_design.constraints.extend(copy_nested_constraints(design1, design2))
    
    return combined_design



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

    eval([design1, design2])

    # Calculate the total number of groups in the combined design
    total_groups = len(design1.groups) * len(design2.groups)
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
            combined_design.counterbalanced = True
            if constraint.width and constraint.height:
                combined_design.constraints.append(
                    Counterbalance(
                        constraint.variable,
                        width=constraint.width,
                        height=total_groups,
                        stride=constraint.stride
                    )
                )
            else: 
                combined_design.constraints.append(
                    Counterbalance(
                        constraint.variable,
                        width=width1,
                        height=total_groups,
                        stride=constraint.stride
                    )
                )

        
        if isinstance(constraint, NoRepeat):
            combined_design.constraints.append(
                NoRepeat(
                    constraint.variable,
                    constraint.width,
                    constraint.stride
                )
            )

    
      
    # need to modify out constraint region
    for constraint in design2.constraints:
        if isinstance(constraint, Counterbalance):
            combined_design.counterbalanced = True
            # Add counterbalance constraint for design2 variables
            combined_design.constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=total_conditions,
                    height=total_groups,
                    stride=constraint.stride
                )
            )

        elif isinstance(constraint, StartWith):
                combined_design.constraints.append(
                    StartWith(constraint.variable, constraint.condition)
                )
        
        elif isinstance(constraint, NoRepeat):
        
              combined_design.constraints.append(
                NoRepeat(
                    constraint.variable,
                    constraint.width,
                    constraint.stride
                )
            )
    

      
    for block in design2.constraints:
        if isinstance(block, InnerBlock):
            combined_design.constraints.append(
                InnerBlock(block.variable, block.width, block.height*len(design1.groups), stride = [1, 1])
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(block, OuterBlock):
            combined_design.constraints.append(
                OuterBlock(block.variable, block.width, block.height*len(design1.groups), stride = [1, 1])
            )
    
    return combined_design