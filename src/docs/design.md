# Design Documentation for Experimental Design DSL 
### Problem
how can a user specify their experimental design using primitive operations with logical mappings? 

### Process: 
1. User uses DSL primitive operations like enforce(only(creation), segment) to define a set of possible sequences (ie. {(c1, c2), (c2, c1)})
2. Compile this into logical constraints 
   - this may be equivilant to (c1 or c2) for the current segment
3. Using these constraints, we can determine the satisfyable sequences mentioned in (1)
4. Then, we test if these sequences satisfy given axioms: is it within-participant, between-participant, latin-square, randomized? etc...

## Primitive Operations

#### `block_length(e, n)` enforces the number of conditions that a participant sees
1. defaults
   -  `n = 1` (each unit assigned one condition)
2. constraints 
   - `if n != 1`, then `n % len(conditions) == 0`; the block length must be a multiple of the number conditions so that the user sees each condition the same amount of times
   - `if n == 1`, then the experiment must satisfy the between-participant constraints 
3. @param e is the experiment

#### `block_segment(block, start:end)` Creates a split in the block represented as valid indices to perform operations on. I think of this like pointers to valid different indices of the block array

1. example:  
    ```python
    block_length(e, 4)
    block = get_block(e) -> [None, None, None, None]
    segment = block_segment(block, 0:2)
    ```
2. When you reference segment, you reference the block array, but you get array out of bounds when ```index < 0 or index > 2 ```
3. this allows users to define constraints on specific segments in the array

#### Groups
1. groups are a construct that allow users to match tasks/conditions with overlapping features
2. example
    
    ```python
    tasks = list(c1, c2, e1, e2)
    creation = list(c1, c2) 
    ```
    notice that creation is a subset of all tasks

3. you can think of a group as a logical formula of `Or(c1, c2)` for the specific example or more generally: `Or([task for task in group])`

4. groups can have overlapping tasks

#### `only(group, segment=block)` returns a logical constraints indicating that you can only pick elements from the specified `group` when you are picking an element in a given `segment`. `segment` defaults to the entire block of tasks
1. example
    ```python
    only(creation, segment = seg1)
    ```
    ouput: `Implies(in_segment(index, seg1), Or(c1, c2))`
    in natural language:   
    
    if the block index we are selecting for is in the specified segment, then pick a creation task

#### `share_group(b1, b2, group_options = list())` returns a constraint where the second parameter b2 is part of the same group as b1. 
1. Only applies to groups expecified in options. 
2. `group_options` defaults to all groups
3. example: 
    ```python
    group1 = list(c1, e1)
    group2 = list(c2, e2)
    share_group(block[2], block[0], group_options = list(group1, group2))
    ```
4. returns constraint on block[2]
    ```python

    Implies(
        block_index == 2,
        And(
            Implies(
                in_group(
                    block[0], 
                    group1
                ), 
                Or(c1, e1)
            ),
            Implies(
                in_group(
                    block[0], 
                    group2
                ), 
                Or(c2, e2)
            )
        )
    )
    ```
    note: in group returns `True` if a given task is in a specified group

5. benefits: allows users to randomize within a segment and apply this pattern
6. concerns: More if/implies patterns to match: less efficient, constraints are clunky and less readable 

## SAT solver axioms 
The first model sets a task variable to true `(c1 == True)` if we can pick this variable for the current index in the block. Because we cannot pick more than two tasks for a block, we nned to ensure that the model is only satisfiable if when a object representing a task is true, no other object representing a task object is true

### example
for tasks `(c1, c2)`
we have `c1 or c2` when there are no other constraints. However, this an return `(c1 = True, c2 = True)`, which is not possible in our case. To fix this, we can set: (c1 and not(c2)) or (c2 and not(c1))

notice: this looks like xor, but we represent using and and or because this can applies to multiple inputs and we don't want an addition modulo two funtionality. 
