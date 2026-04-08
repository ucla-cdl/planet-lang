from planet import *
from planet.analysis import Analysis

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

test = ExperimentVariable(
    name = "test",
    options = ["x", "y"]
)

test2 = ExperimentVariable(
    name = "test2",
    options = ["X", "Y"]
)

des1 = (
    Design()
        .between_subjects(treatment)
        .counterbalance(treatment)
        # .limit_plans(2)
)

des2 = (
    Design()
        .between_subjects(task)
        .counterbalance(task)
        # .limit_plans(2)
)


units = Units(48)

des = nest(inner=des2, outer=des1)

# mega.to_latex()
print(assign(units, des))
print(Analysis(des))