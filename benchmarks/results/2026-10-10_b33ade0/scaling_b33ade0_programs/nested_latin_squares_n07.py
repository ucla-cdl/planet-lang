from planet import *
import math

n = 7
outer_var = ExperimentVariable("outer", options=[f"o{i}" for i in range(n)])
inner_var = ExperimentVariable("inner", options=[f"i{i}" for i in range(n)])
outer = (
    Design()
        .within_subjects(outer_var)
        .counterbalance(outer_var)
        .limit_plans(n)
)
inner = (
    Design()
        .within_subjects(inner_var)
        .counterbalance(inner_var)
        .limit_plans(n)
)
design = nest(inner=inner, outer=outer)
assign(Units(n * n), design)
