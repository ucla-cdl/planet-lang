import os
import sys
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design
from lib.unit import Units 
from lib.assignment import assign 
from lib.replications import Replications
from lib.nest import nest

"""
https://dl.acm.org/doi/pdf/10.1145/3613904.3641907
"""

# NOTE: fix bug :) 

shape = ExperimentVariable("shape", options=["large", "small",
                                            #  ])
                                              "horizontal", "vertical", "triangle"])

participants = Units(12) 
repititions = Replications(3)

design = (
    Design()
    .within_subjects(shape)
    # .counterbalance(shape)
)
 
#FIXME: small bug
final = nest(outer=repititions, inner=design)
print(assign(participants, final))