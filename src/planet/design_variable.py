class DesignVariable:
    def __init__(self, variable):
        self.variable = variable
        self.constraint_spec = {
            "Counterbalance":None,
            "NoRepeat":None,
            "AbsoluteRank":None,
            "OuterBlock":None,
            "InnerBlock":None,
        }

    def add_constraint(self, constraint):
        if self.constraint_spec[constraint.__class__.__name__] is None:
            self.constraint_spec[constraint.__class__.__name__] = constraint

    def has(self, constraint_name):
        return self.constraint_spec.get(constraint_name) is not None
    
    def get_ranks(self):
                # count_values(constraint.ranks)
        return self.constraint_spec.get("AbsoluteRank").ranks

    @property
    def is_counterbalanced(self):
        return self.has("Counterbalance")

    @property
    def is_repeated(self):
        return self.has("NoRepeat")

    @property
    def is_ranked(self):
        return self.has("AbsoluteRank")

    @property
    def is_blocked_outer(self):
        return self.has("OuterBlock")

    @property
    def is_blocked_inner(self):
        return self.has("InnerBlock")

    @property
    def is_random(self):
        return not (
            self.is_counterbalanced
            or self.is_ranked
        )
        