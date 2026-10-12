from planet import *
import math

n, k = 12, 4
cond = ExperimentVariable("cond", options=[f"c{i}" for i in range(n)])
latin = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(n)
)
repeat = Design().num_trials(k)
design = nest(inner=repeat, outer=latin)
assign(Units(n), design)
