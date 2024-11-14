import itertools
from .variable import ExperimentVariable
from.condition import ExperimentCondition
import numpy as np

# cartesian product of variable conditions to form experimental conditions
def conditions_from_vars(*argv):

    for arg in argv:
        assert isinstance(arg, ExperimentVariable)

    variable_conditions = [arg.conditions for arg in argv]
    conditions = list(itertools.product(*variable_conditions))

    conditions = [ExperimentCondition(f"condition{i+1}", *conditions[i]) for i in range(len(conditions))]



    return conditions


# move out of this class
def shape_array(arr, shape):
    return np.array(arr).reshape(shape).tolist()

def flatten_array(arr):
    return np.array(arr).flatten().tolist()





    