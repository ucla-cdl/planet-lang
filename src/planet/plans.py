from dataclasses import dataclass, field
import hashlib
from planet.designer import Designer

class Plans:
    def __init__(self, plan_matrix, constraints, trials, groups, variable_ids):
        self.plan_matrix = plan_matrix
        self.constraints = constraints  # tuple of stringified constraint IDs
        self.trials = trials
        self.groups = groups
        self.variable_ids = variable_ids  # tuple of variable IDs or names


    # @classmethod
    # def from_design(cls, design):
    #     # 1. Run the solver on the design
    #     plan_matrix = Designer().solve(design
    #     # 2. Instantiate a Plans object with results
    #     return cls(plan_matrix, design)

    def snapshot(self):
        groups = len(self.groups)
        constraint_ids = self.constraints.stringified()
        signature = "_".join(constraint_ids) + f"_{self.get_width()}_{groups}"
        return hashlib.sha256(signature.encode()).hexdigest()

    def _eval_plans(self, n = None):
    
        if self.is_empty:
            return []
        
        elif self.is_random:
            prev = len(self.groups)
            self.groups.set_num_plans(1)
     
        self.eval()
        self.previous_snapshot = self.snapshot()

        random_variables = self.identify_random_vars()
        if len(random_variables):
            assert n is not None
            n = math.ceil(n/len(self.plans)) * len(self.plans)
            for rand in random_variables:
                self._instantiate_random_variables(n, rand)

        if self.is_random:
            self.groups.set_num_plans(prev)


    def extract_counterbalance_info(self, var):
        """Extract variables and condition count"""
        return (len(var.get_variables()), len(var))
    
 
    def _eval(self):
        # Get the width of the design
        width = self.get_width()
        sequence = Sequence(width)
        self._determine_num_plans()
        

        self.designer.start(
            self.groups, 
            sequence, 
            self.variables
        )

        
        # NOTE: ensure no downstream effects :)
        # self.designer.solver.all_different()
        self.designer.eval_constraints(self.constraints.get_constraints(), self.groups, width)

    def test_eval(self):
        self._eval()
        return self.designer.eval_all()
        

    def eval(self):
        assert not self.is_empty
        self._eval()
        plans = self.designer.eval()
        self.plans = plans