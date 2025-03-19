from z3 import *
from lib.unit import Groups
from lib.orders import Sequence
from lib.assignment import Assignment
import math

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


class Block:
    """Represents a block structure in the experimental design."""
    def __init__(self, variable, width, height, v2):
        self.variable = variable
        self.width = width
        self.height = height
        self.v2 = v2

class NoRepeat:
    def __init__(self, variable=None, width = None):
        self.variable = variable

        if width is None:
            self.width = len(variable)
        else:
            self.width = width


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
        self.match_constraints = []
        self.trials = 0

        self.ws_count = 0
  

    def num_trials(self, n):
        self.trials = n
        return self

    def match_block(self, variable, block_width, block_height, v2):

        self.block_width = block_width
        self.block_height = block_height
        self.match_var = variable
        self.match2 = v2

        # Create a new Block object with the provided parameters
        block = Block(variable, block_width, block_height, v2)
        
        # Add the block to the list of match constraints
        self.match_constraints.append(block)
        
        # Debug print of current constraints (consider removing in production)
        
        # Return self for method chaining
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
                assignment.solver.all_different(constraint.variable, constraint.width)
            elif isinstance(constraint, StartWith):
                assignment.start_with(constraint.variable, constraint.condition)
    
        # Process match constraints
        for match_constraint in self.match_constraints:
            assignment.match_inner(
                match_constraint.variable,
                match_constraint.width,
                match_constraint.height,
            )
            assignment.match_outer(
                match_constraint.v2,
                match_constraint.width,
                match_constraint.height,
            )
        
        # Add match blocks for between-subjects variables when there are multiple variables
        for variable in self.variables:
            if isinstance(variable.constraint, BetweenSubjects):
                assignment.match_inner(variable, width, 1)

        # Evaluate the assignment and return the result
        result = assignment.eval()

        print(self.groups.n)

        return result
        
    def counterbalance(self, *variable, w = 0, h = 0, stride = [1, 1]):


        print(list(variable))

        if len(variable) == 1:
            self.constraints.append(NoRepeat(variable[0]))
        self.constraints.append(Counterbalance(variable, width = w, height = h, stride = stride))
        return self


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

    print(design2.groups.n)
    # Calculate the total number of groups in the combined design
    total_groups = len(design1.groups) * len(design2.groups)
    
    # Combine variables from both designs
    combined_variables = design1.variables.copy()
    combined_variables.extend(design2.variables)
    
    # Calculate the total number of conditions
    total_conditions = 1
    for variable in combined_variables:
        total_conditions *= len(variable)
    
    # Get the first constraint from design1
    constraint1 = design1.constraints[0]
    
    # Calculate width_test (the product of all variable lengths in design1)
    width_test = 1

    if design1.trials == 0:
        for variable in design1.variables:
            width_test *= len(variable)
    else: 
        width_test = design1.trials

    print(width_test)
    
    # Create a new design with the combined variables
    combined_design = Design().within_subjects(*combined_variables).limit_groups(total_groups).num_trials(width_test * 2)
    # Add the first match block

    combined_design.match_block(
        design2.variables[0],
        width_test,
        len(design1.groups),
        design1.variables[0]
    )
    
    # Add the second match block if design1 has more than one variable
    if len(design1.variables) > 1:
        combined_design.match_block(
            design2.variables[0],
            width_test,
            len(design1.groups),
            design1.variables[1]
        )
    
    # Add counterbalance constraints from design1
    for constraint in design1.constraints:
        if isinstance(constraint, Counterbalance):

            combined_design.constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=constraint.width,
                    height=constraint.height,
                    stride=[1, 1]
                )
            )
        
        if isinstance(constraint, NoRepeat):
            combined_design.constraints.append(
                NoRepeat(
                    constraint.variable,
                    constraint.width
                )
            )
      
    
    for constraint in design2.constraints:
        if isinstance(constraint, Counterbalance):
            # Add counterbalance constraint for design2 variables
            combined_design.constraints.append(
                Counterbalance(
                    design2.variables,
                    width=total_conditions,
                    height=total_groups,
                    stride=[width_test, len(design1.groups)]
                )
            )

        elif isinstance(constraint, StartWith):
                combined_design.constraints.append(
                    StartWith(constraint.variable, constraint.condition)
                )
    
    # Copy match constraints from design1 if they exist
    if design1.match_constraints:
        block = design1.match_constraints[0]
        combined_design.match_constraints.append(
            Block(block.variable, block.width, block.height, block.v2)
        )
    
    return combined_design