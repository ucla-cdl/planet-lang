from planet import *

# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
treatment = ExperimentVariable( 
    name = "treatment",
    options = ["A", "B"]
)
task = ExperimentVariable(
    name = "task",
    options = ["a", "b"]
)



des1 = (
    Design()
        .within_subjects(treatment)
        # .counterbalance(treatment)
)

des2 = (
    Design()
        .within_subjects(task)
        # .counterbalance(task)
        # .absolute_rank(task, "a", 1)
)

units = Units(4)


des = nest(inner=des2, outer=des1)
print(assign(units, des))
