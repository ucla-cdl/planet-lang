from z3 import *


class Constraint:
    def __init__(self, variable):
        self.variable = variable

    def get_variable(self):
        return self.variable
    
    def accept(self, visitor, origin):
        return visitor.visit(self, origin)
    

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




class ConstraintCopyVisitor:
    def __init__(self, design1, design2):
        self.design1 = design1
        self.design2 = design2
        self.width1 = design1.get_width()
        self.width2 = design2.get_width()
        self.total_groups = len(design1.groups) * len(design2.groups)
        self.total_conditions = self.width1 * self.width2
        self.constraints = []

    def visit(self, constraint, origin):
        method_name = f'visit_{constraint.__class__.__name__}'
        visitor = getattr(self, method_name, self.visit_default)
        return visitor(constraint, origin)

    def visit_Counterbalance(self, constraint, origin):
        if origin == 'design1':
            width = constraint.width or self.width1
            height = constraint.height or len(self.design1.groups)
            self.constraints.append(
                Counterbalance(
                    constraint.variable, width=width, height=height, stride=constraint.stride
                )
            )
        elif origin == 'design2':
            self.constraints.append(
                Counterbalance(
                    constraint.variable,
                    width=self.total_conditions,
                    height=self.total_groups,
                    stride=[len(self.design1.groups), self.width1 * constraint.stride[1]]
                )
            )

    def visit_NoRepeat(self, constraint, origin):
        if origin == 'design1':
            print(self.width1)
            self.constraints.append(
                NoRepeat(constraint.variable, width=self.width1, stride=constraint.stride)
            )
        elif origin == 'design2':
            self.constraints.append(
                NoRepeat(
                    constraint.variable,
                    width=constraint.width * self.width1,
                    stride=constraint.stride * self.width1
                )
            )

    def visit_InnerBlock(self, constraint, origin):
        self.constraints.append(
            InnerBlock(
                constraint.variable,
                width=constraint.width * self.width1,
                height=constraint.height * len(self.design1.groups),
                stride=[1, 1]
            )
        )

    def visit_OuterBlock(self, constraint, origin):
        self.constraints.append(
            OuterBlock(
                constraint.variable,
                width=constraint.width * self.width1,
                height=constraint.height * len(self.design1.groups),
                stride=[1, 1]
            )
        )

    def visit_default(self, constraint, origin):
        self.constraints.append(copy.copy(constraint))


 