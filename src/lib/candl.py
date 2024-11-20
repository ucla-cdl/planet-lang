import itertools
from .variable import ExperimentVariable
from.condition import ExperimentCondition
import numpy as np
from itertools import product
import math

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

def create_indexing(dim, dims):
    dim_indexings = []
    # combination of all levels of each dimension, except for the one 
    # we want to put a constraint on
    keys = list(product(*[set(range(dims[i])) for i in range(len(dims)) if i != len(dims) - 1 - dim]))
    
    # this whole thing is a paradigm that I should be able
    # to use for various tasks
    for tup in keys:
        indexing = []
        count = 0
        for index in range(len(dims)):
            if index == dim:
                indexing.append(slice(None))
            else:
                indexing.append(tup[count])
                count += 1
        indexing.reverse()
        dim_indexings.append(indexing)

    return dim_indexings


def get_elements_of_dim(arr, shape, indexing):
    return np.array(arr).reshape(shape)[*indexing].tolist()

def all_elements_of_dim(dim, arr, shape):
    dim_indexings = create_indexing(dim, shape)

    dim_variables = []
    for indexing in dim_indexings:
        dim_variables.append(get_elements_of_dim(arr, shape, indexing))

    return dim_variables

def get_num_bits(n):
    return int(round(math.log(n, 2)))

def all_ones(n):
    return (1 << n) - 1



    