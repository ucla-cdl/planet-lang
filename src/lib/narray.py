from itertools import product
from z3 import *

def add_dimension(dims, unit_variables):
    if len(unit_variables) == 1:
        return [f"unit_" for i in range(dims[0])]
    
    else:
        return [add_dimension(dims[1:], unit_variables[1:]) for i in range(dims[0])]
    
def get_narray_elem(indices, narray):
    curr = narray
    i = 0
    while type(curr) == list:
        curr = curr[indices[i]]
        i += 1

    return curr

def modify_narray_elem(indices, narray, f):
    curr = narray
    i = 0
    arr = None
    while type(curr) == list:
        arr = curr
        curr = curr[indices[i]]
        i += 1

    arr[indices[i-1]] =  f(indices[i-1], arr)

    return narray

def str_from_list(l):
    ret = ""
    for s in l:
        ret+=str(s+1)
    return ret

def construct_units(narray, dims):
    keys = list(product(set(range(dims[0])), set(range(dims[1]))))
  
    for key in keys:
        add = lambda i, arr : arr[i] + str_from_list(key)
        narray = modify_narray_elem(key, narray, add)

    return narray

def construct_z3(narray, dims):
    keys = list(product(set(range(dims[0])), set(range(dims[1]))))
    z3_fun = lambda i, arr : Int(arr[i]) 
    for key in keys:
        narray = modify_narray_elem(key, narray, z3_fun)

    return narray

