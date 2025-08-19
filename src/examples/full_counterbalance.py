from planet import *

treatment = ExperimentVariable(
    name = "treatment",
    options = ["a", "b", "c", "d"]
)

units = Units(48)


des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
        .num_trials(3)
    
)

assignment = assign(units, des)

print(assignment)

