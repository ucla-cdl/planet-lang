from planet import *
import math

n, p = 5, 20
cond = ExperimentVariable("cond", options=[f"c{i}" for i in range(n)])
design = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(p)
)
assign(Units(p), design)
