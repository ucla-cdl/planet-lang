from planet import *
import math

n = 11
a = ExperimentVariable("a", options=[f"a{i}" for i in range(n)])
b = ExperimentVariable("b", options=[f"b{i}" for i in range(n)])
da = (
    Design()
        .within_subjects(a)
        .counterbalance(a)
        .limit_plans(n)
)
db = (
    Design()
        .within_subjects(b)
        .counterbalance(b)
        .limit_plans(n)
)
design = cross(da, db)
assign(Units(n * n), design)
