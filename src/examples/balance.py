import sys
sys.path.append("../")

from z3 import *
from lib.variable import ExperimentVariable
from lib.design import Design
from lib.unit import Units
from lib.assignment import assign



count = ExperimentVariable(
    name = "count",
    options = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "10"]
)

units = Units(20)

des = (
    Design()
        .within_subjects(count)
        .counterbalance(count)
        .limit_groups(len(count) * 2)
)


print(assign(units, des))










# # Now, how to actually assign the values?

# # new counterbalance: select sections of table and cross join by random. This makes more sense than 
# # making a special table. Port orders into a table with an id? Counterbalanced assignment might be kind
# # of tricky... 

# # NOTE: currently not supporting blocking. Keep assignment but select units 
# in table who have a certain attr only and then modify table. In every round no matter attr select units 
# who have NULL as assignment 

# How should we be handling clusters and quasi-experimental assignment? I think we should leave
# this out for the scope of the project. 