from z3 import *

sys.path.append("../")

from lib.variable import ExperimentVariable
from lib.design import Design
from lib.unit import Units
from lib.assignment import assign
import time


count = ExperimentVariable(
    name = "count",
    options = ["1", "2", "3", "4", "5", "6", "7", "8"]
)

units = Units(8)



des = (
    Design()
        .within_subjects(count)
        .counterbalance(count)
        .limit_groups(len(count))
)

t = time.time()
des.to_latex()
print(assign(units, des))
print(time.time() - t)

