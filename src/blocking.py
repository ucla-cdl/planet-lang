from lib.orders import Groups
from lib.assignment import Assignment
from lib.unit import Units
from lib.variable import ExperimentVariable, UnitVariable


# user creates one variable treatment 
treatment = ExperimentVariable(
    name = "treatment",
    options = ["ffl", "latex", "manual"]
)

age = UnitVariable(
    name = "age",
    levels = ["young", "old"]
)

# all 20 units associated with id = i
units = Units(20)
units.block(age, split=.5)
# this experiment has one varibable and three 
# conditions of the variable, resulting in 3 groups
groups = Groups(treatment) 

units.assign(groups)



