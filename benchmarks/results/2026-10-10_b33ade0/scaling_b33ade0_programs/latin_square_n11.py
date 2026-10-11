from planet import *
import math

n = 11
cond = ExperimentVariable("cond", options=[f"c{i}" for i in range(n)])
design = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
        .limit_plans(n)
)
assign(Units(n), design)
