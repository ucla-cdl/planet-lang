from planet import *
import math
import time 

tool = ExperimentVariable(
    name = "tool",
    options = [f"baseline{i}" for i in range(1, 8)]
)

# task = ExperimentVariable(
#     name = "task",
#     options = [f"task{i}" for i in range(1, 4)]
# )

participants = Units(7)
design = (
    Design()
        .within_subjects(tool)
#         .absolute_rank(tool, "baseline1", 1)
#         .absolute_rank(tool, "baseline2", 1)

        .counterbalance(tool)
        .limit_plans(7**3*2)
)

# d2 = (
#     Design()
#         .within_subjects(task)
#         .counterbalance(task)
# )

# design = cross(d2, design)

assign(participants, design)