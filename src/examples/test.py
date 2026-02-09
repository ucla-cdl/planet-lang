import sys
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

num = ExperimentVariable(
    name = "num",
    options = ["1", "2"]
)
# rep = Replications(2)



des1 = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
)

des2 = (
    Design()
        .within_subjects(task)
        .absolute_rank(task, "a", 1)
)

des3 = (
    Design()
        .within_subjects(num)
)


units = Units(10)



print("\n\n\n")
print("performing proper nest")

des = nest(inner=des1, outer=des2)
# mega = nest(inner=des3, outer=des)
# # mega.to_latex()
# print("step2")

final = assign(units, des)
# # print("step3")
print(final)
# print(assign(units, des1))

