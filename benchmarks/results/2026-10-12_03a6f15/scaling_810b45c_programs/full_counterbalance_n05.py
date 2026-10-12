from planet import *
import math

n = 5
cond = ExperimentVariable("cond", options=[f"c{i}" for i in range(n)])
design = (
    Design()
        .within_subjects(cond)
        .counterbalance(cond)
)
assign(Units(math.factorial(n)), design)
