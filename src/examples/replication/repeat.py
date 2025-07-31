from planet import *

x = ExperimentVariable(
    name = "x",
    options = ["a", "b"] 
)
replications = (
    Design()
        .num_trials(2)
)

units = Units(24)

des = (
    Design()
        .within_subjects(x)
        .counterbalance(x)
)


final = nest(inner=replications, outer=des)
assignment = assign(units, final)
print(assignment)
