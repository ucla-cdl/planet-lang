import itertools
from .variable import ExperimentVariable, MultiFactVariable
from.condition import ExperimentCondition
import numpy as np
from itertools import product, combinations
import math
from z3 import *
import random



def at_least_one_diff(variables):
    """Generate constraints that enforce every pair of variable assignments
    differ in at least one position."""
    constraints = []
    for var1, var2 in combinations(variables, 2):
        # For each pair, at least one element differs
        constraints.append(Or([a != b for a, b in zip(var1, var2)]))
    return constraints

def generate_conditions(participants, variable, n):
    """
    Generates a randomized sequence of conditions for each participant.
    
    :param participants: Number of participants
    :param conditions: List of conditions
    :param trials_per_condition: Number of times each condition should appear
    :return: Dictionary mapping participant IDs to their condition sequences
    """
   
    experiment_data = []
    if variable: 
        conditions = variable.conditions
        for _ in range(participants):
            # FIXME: path for random multifactorial variables
            experiment_data.append(random.sample(conditions, n))
   

    return experiment_data


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

# FIXME
def create_indexing(dim, dims):
    dim_indexings = []
    # combination of all levels of each dimension, except for the one 
    # we want to put a constraint on
    keys = list(product(*[set(range(dims[i])) for i in range(len(dims)) if i != dim]))

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
     
        dim_indexings.append(indexing)

    return dim_indexings


def create_indexing_2(dim, dims):
    dim_indexings = []

    # this whole thing is a paradigm that I should be able
    # to use for various tasks
    for val in range(dims[dim]):
        indexing = []
        for index in range(len(dims)):
            if index == dim:
                indexing.append(val)
            else:
                indexing.append(slice(None))
     
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
    return int(math.ceil(math.log(n, 2)))

def all_ones(n):
    return (1 << n) - 1


def get_dim_variables(arr, shape, dim, factor = None, level = None):
    if factor != None:
        dim_indexings = create_indexing_2(factor, shape)
        indexing = dim_indexings[level]

        arr_to_constrain = get_elements_of_dim(arr, shape, indexing)
        arr_to_constrain = flatten_array(arr_to_constrain)
       

        shape = tuple([shape[i] for i in range(len(shape)) if i != factor])
     
        dim_variables = all_elements_of_dim(dim - 1, arr_to_constrain, shape)

    else:
        dim_variables = all_elements_of_dim(dim, arr, shape)

    return dim_variables


def shape_array(arr, shape):
    return np.array(arr).reshape(shape)

def combine_lists(l1, l2):
    combined_variables = l1.copy()
    combined_variables.extend(l2)

    return combined_variables

def create_directory_for_file(filepath):
    directory = os.path.dirname(filepath)
    if directory:
        os.makedirs(directory, exist_ok=True)


def as_list(variables):
    if isinstance(variables, list):
        return variables
    else:
        return [variables]
    


def count_values(d: dict) -> dict:
    """Count the frequency of values in a dictionary."""
    counts = {}
    for value in d.values():
        counts[value] = counts.get(value, 0) + 1
    return counts


def factorial_product_of_counts(counts: dict) -> int:
    """Return the product of factorials of all counts."""
    return math.prod(math.factorial(count) for count in counts.values())

def calculate_plan_multiplier(num_conditions: int, num_vars: int, num_trials: int) -> float:
    """Compute the multiplier for total_n_plans based on design width and condition count."""
    if num_conditions == 1:
        return 1
    if num_trials > num_conditions:
        num_repeats = int(num_trials / num_conditions)
        denom = math.prod(math.factorial(num_repeats) for _ in range(num_vars))
        return math.factorial(num_conditions) / denom
    elif num_trials < num_conditions:
        return math.factorial(num_conditions) / math.factorial(num_conditions - num_trials)
    else:
        return math.factorial(num_conditions)


def partition_matrix_by_columns(matrix, width, step=1):
    return np.array(matrix)[:, 0:width:step]