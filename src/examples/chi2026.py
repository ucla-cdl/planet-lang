from planet import *

tool = ExperimentVariable(
    name = "tool",
    options = ["baseline", "latex"]
)
task = ExperimentVariable(
    name = "task",
    options = ["writing", "editing"]
)

participants = Units(12)
design = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)

d2 = (
    Design()
        .within_subjects(tool)
        .absolute_rank(tool, "baseline", 1)
)

design = nest(outer=d2, inner=design)

print(assign(participants, design))