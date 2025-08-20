from z3 import *

import sys
sys.path.append("../")
from lib.variable import ExperimentVariable
from lib.design import Design, nest
from lib.assignment import assign, assign_counterbalance
from lib.unit import Units, Clusters



treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c"]
)

units = Units(24)

clusters = Clusters(units, 6)


des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
        .limit_plans(len(treatment))
)

print(assign(clusters, des))

