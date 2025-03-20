from z3 import *
from lib.unit import Groups
from lib.orders import Sequence
from lib.assignment import Assignment
import math
import sys

from lib.candl import generate_conditions

class VariableType:
    def __init__(self, variable):
     
        self.variable = variable

    def __len__(self):
        return len(self.variable) 
    

class BetweenSubjects(VariableType):
    """Variable that varies between subject groups."""
    def __init__(self, variable):
        super().__init__(variable)
        self.n = 1

class WithinSubjects(VariableType):
    """Variable that varies within subject groups."""
    def __init__(self, variable):
        super().__init__(variable)
        self.n = math.prod([len(v) for v in variable])


class InnerBlock:
    """Represents a block structure in the experimental design."""
    def __init__(self, variable, width, height, stride):
        self.variable = variable
        self.width = width
        self.height = height
        self.stride = stride

class OuterBlock:
    """Represents a block structure in the experimental design."""
    def __init__(self, variable, width, height, stride):
        self.variable = variable
        self.width = width
        self.height = height
        self.stride = stride

    def __str__(self):
        return f"{self.variable}: \n\t{self.width}\n\t{self.height}\n"

class NoRepeat:
    def __init__(self, variable=None, width = None, stride = 1):
        self.variable = variable

        if width is None:
            self.width = len(variable)
        else:
            self.width = width

        self.stride = stride


class Counterbalance:
    """Defines counterbalancing for variables."""
    def __init__(self, variable, width=0, height=0, stride=(1, 1)):
        self.variable = variable
        self.width = width
        self.height = height
        self.stride = stride

    def __str__(self):
        return f"COUNTERBALANCE: {self.width, self.height, self.stride}"
    
class StartWith:
    def __init__(self, variable, condition):
        self.variable = variable
        self.condition = condition

class Design:
    """Main class for creating experimental designs."""
    def __init__(self):
        self.sequence = None
        self.variables = []
        self.groups = None
        self.constraints = []
        self.trials = 0

        self.counterbalanced = False
  

    def num_trials(self, n):
        self.trials = n
        return self
    
    def between_subjects(self, *variables):
        
        for v in variables:
            self.variables.append(v)
            v.add_constraint(BetweenSubjects(v))
    
        return self

    def within_subjects(self, *variables):
        
        # Add all variables to the instance's variables list
        self.variables.extend(variables)
        
        # Apply WithinSubjects constraint to each variable
        # Note: We pass all variables to each WithinSubjects constructor
        for x in variables:
            x.add_constraint(WithinSubjects([variables]))
        
        return self
    
    def limit_groups(self, n):
        self.groups = Groups(n)
        return self
    
    def get_width(self):
        if self.trials:
            return self.trials

        n = 1
        for v in self.variables:
            if isinstance(v.constraint, WithinSubjects):
                n *= v.n
        
        return n
    
    
    def start_with(self, variable, condition):
        self.constraints.append(StartWith(variable, condition))
        return self

    
    def eval(self):
        
        """
        Evaluate the experimental design and generate a solution.
        
        Returns:
            The evaluation result from the Assignment solver
        """
        # Get the width of the design
        width = self.get_width()
        sequence = Sequence(width)

        if self.groups is None:
            self.groups = Groups(0)
       
        # Create assignment with groups, sequence, and flattened variables
        assignment = Assignment(self.groups, sequence, variables=self.variables)
        assignment.solver.all_different()
    
        # Process counterbalance constraints
        for constraint in self.constraints:

            if isinstance(constraint, Counterbalance):
                if len(self.groups):
                    # Set default width and height if not specified
                    if not constraint.width:
                        constraint.width = width
                    if not constraint.height:
                        constraint.height = len(self.groups)
                    
                    # Apply counterbalance to the assignment
                    assignment.counterbalance(
                        constraint.variable, 
                        w=constraint.width, 
                        h=constraint.height, 
                        stride=constraint.stride
                    )
            elif isinstance(constraint, NoRepeat):
                assignment.solver.all_different(constraint.variable, constraint.width, constraint.stride)
            elif isinstance(constraint, StartWith):
                assignment.start_with(constraint.variable, constraint.condition)
    
     
            elif isinstance(constraint, InnerBlock):
                assignment.match_inner(
                    constraint.variable,
                    constraint.width,
                    constraint.height,
                )

            else:
                assignment.match_outer(
                    constraint.variable,
                    constraint.width,
                    constraint.height,
                )
        
        # Add match blocks for between-subjects variables when there are multiple variables
        for variable in self.variables:
            if isinstance(variable.constraint, BetweenSubjects):
                assignment.match_inner(variable, width, 1)

        # Evaluate the assignment and return the result
        result = assignment.eval()
        return result
        
    def counterbalance(self, *variable, w = 0, h = 0, stride = [1, 1]):
        self.counterbalanced = True

        self.constraints.append(NoRepeat([variable], width=len(variable[0])))

        self.constraints.append(Counterbalance(variable, width = w, height = h, stride = stride))
        return self
    
    def random(self, units):
        return generate_conditions(units.n, self.variables[0].conditions)


    def __str__(self):
        matrix = self.eval()

        ret = "Experiment Plans: \n \n"

        for i in range(len(matrix)):
            ret += f"plan {i+1}:\n\t" 
            for j in range(len(matrix[i])):

                end = "" if j == len(matrix[i]) - 1 else "\t" 
                conditions = matrix[i][j].split("-")

                test = [f"{self.variables[x].name} = {conditions[x]}" for x in range(len(conditions))]
                conditions = ", ".join(test)

                ret += f"trial {j+1}: {str(conditions)}\n" + end



        return ret




def nest(design1, design2):
    """
    Nest two designs together to create a combined experimental design.
    
    Args:
        design1: First design object
        design2: Second design object
        
    Returns:
        Combined design object
    """

    if design2.groups is None:
        design2.eval()

    if design1.groups is None:
        design1.eval()

    # Calculate the total number of groups in the combined design
    total_groups = len(design1.groups) * len(design2.groups)
    
    # Combine variables from both designs
    combined_variables = design1.variables.copy()
    combined_variables.extend(design2.variables)
    
    # Calculate width_test (the product of all variable lengths in design1)
    width_test = design1.get_width()

    width2 = design2.get_width()
    total_conditions = width2 * width_test
    
    # Create a new design with the combined variables
    combined_design = Design().within_subjects(*combined_variables).limit_groups(total_groups).num_trials(total_conditions)
   
    # Add the first match block
    for i in range(len(design2.variables)):
        combined_design.constraints.append(InnerBlock(
            design2.variables[i],
            width_test,
            len(design1.groups),
            stride = [1, 1]
        ))

     # Add the first match block
    for i in range(len(design1.variables)):
        combined_design.constraints.append(OuterBlock(
            design1.variables[i],
            width_test,
            len(design1.groups),
            stride = [1, 1]
        ))
  
    # Add counterbalance constraints from design1
    for constraint in design1.constraints:
        if isinstance(constraint, Counterbalance):
            combined_design.counterbalanced = True


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
                        width=width_test,
                        height=len(design1.groups),
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
      
    
    for constraint in design2.constraints:
        if isinstance(constraint, Counterbalance):
            combined_design.counterbalanced = True
            # Add counterbalance constraint for design2 variables
            combined_design.constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=total_conditions,
                    height=total_groups,
                    stride=[width_test*constraint.stride[0], len(design1.groups)*constraint.stride[1]]
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
                    constraint.width*width_test,
                    width_test*constraint.stride
                )
            )
    
    # # Copy match constraints from design1 if they exist
    for block in design1.constraints:
        if isinstance(block, InnerBlock):
            combined_design.constraints.append(
                InnerBlock(block.variable, block.width, block.height, stride = [1, 1])
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(block, OuterBlock):
            combined_design.constraints.append(
                OuterBlock(block.variable, block.width, block.height, stride = [1, 1])
            )

      
    for block in design2.constraints:
        if isinstance(block, InnerBlock):
            combined_design.constraints.append(
                InnerBlock(block.variable, block.width*width_test, block.height*len(design1.groups), stride = [1, 1])
            )

        # # here I need to multiply stride by the number of conditions of the block variable
        elif isinstance(block, OuterBlock):
            combined_design.constraints.append(
                OuterBlock(block.variable, block.width*width_test, block.height*len(design1.groups), stride = [1, 1])
            )
    
    return combined_design