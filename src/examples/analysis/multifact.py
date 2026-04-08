from planet import *
from planet.analysis import Analysis
import time


treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b"]
)

task = ExperimentVariable(
    name = "task",
    options = ["1", "2"]
)

test = ExperimentVariable(
    name = "test",
    options = ["x", "y"]
)

test = multifact([treatment, task, test])

des = (
    Design()
        .within_subjects(test)
        .counterbalance(test)
        .limit_plans(8)
)

# NOTE: fixme! This does not round up :o
units = Units(1)
t1 = time.time()
print(assign(units, des))
print(time.time() - t1)
print(Analysis(des))