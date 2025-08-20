from z3 import *


class Constraint:
    def __init__(self, variable):
        self.variable = variable

    def get_variable(self):
        return self.variable
    

class BlockConstraint(Constraint):
    def __init__(self, variable, width, height, stride):
        super().__init__(variable)
        self.width = width
        self.height = height
        self.stride = stride

class PlanConstraint(Constraint):
    def __init__(self, variable, width, stride):
        super().__init__(variable)
        self.stride = stride
        self.width = width


class InnerBlock(BlockConstraint):
    """Represents a block structure in the experimental design."""
    def __init__(self, variable, width, height, stride= [1,1]):
        super().__init__(variable, width, height, stride)

class OuterBlock(BlockConstraint):
    """Represents a block structure in the experimental design."""
    def __init__(self, variable, width, height, stride):
        super().__init__(variable, width, height, stride)

    def __str__(self):
        return f"{self.variable}: \n\t{self.width}\n\t{self.height}\n"

class NoRepeat(PlanConstraint):
    def __init__(self, variable, width= None, stride= 1):
        if width is None:
            width = len(variable)
        super().__init__(variable, width, stride)

   
class Counterbalance(BlockConstraint):
    """Defines counterbalancing for variables."""
    def __init__(self, variable, width=0, height=0, stride=(1, 1)):
        super().__init__(variable, width, height, stride)
 
    def __str__(self):
        return f"COUNTERBALANCE: {self.width, self.height, self.stride}"
    
class StartWith(Constraint):
    def __init__(self, variable, condition):
        super().__init__(variable)
        # FIXME: modifying variables to contain list
        self.condition = condition

class SetRank(Constraint):
    def __init__(self, variable, condition, rank, condition2):
        super().__init__(variable)
        self.condition = condition
        self.rank = rank
        self.condition2 = condition2 

    
class AbsoluteRank(Constraint):
    def __init__(self, variable, condition, rank):
        super().__init__(variable)
        self.ranks = dict.fromkeys(variable.conditions, 0)
        self.add_rank(condition, rank)

    def add_rank(self, condition, rank):
        self.ranks[condition] = rank

    

class SetPosition(Constraint):
    def __init__(self, variable, condition, pos):
        super().__init__(variable)
        self.condition = condition
        self.position = pos


