from planet import *
import math

n, m = 12, 18
cond = ExperimentVariable("cond", options=[f"c{i}" for i in range(n)])
inner_var = ExperimentVariable("inner", options=[f"i{i}" for i in range(m)])
latin = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(n)
)
inner = Design().within_subjects(inner_var)
design = nest(inner=inner, outer=latin)
assign(Units(n), design)
