# Design Documentation for Experimental Design DSL 
This is documentation for design choices for compiling user-written code into constraints for assignment in experimental design.  

## Representing Variable Conditions 
1. as Bools
2. as Ints
3. as Bitvectors

#### Pros/Cons of (1)
- The most significant drawback is working at the element-level rather than at the "order" level. 
- Requires 2-passes to determine satisfiable order

#### Pros/Cons of (2)
- Integers map directly to condition assignments, but we need a way to maintain this information 
- Most significant pro is ability to work with order-level constraints
- less class scaffolding/contains solver information to one class (order)
- Same operations apply as working with bools for the `different()` and `match()` function calls
- Need a way to represent a total experimental condition (ie. the combination of the condition assignments of all variables)
  - the current design choice is essentially concatenating the values by changing the base to ensure that all combinations of values are unique 
  - this also requires us to introduce an additional n z3 vars, where n is the number of conditions in the order

### Pros/Cons of (3)
- efficiency/memory 
- very similar structure/scaffolding to (2)
- Potential con is the mixed-types inefficiency (but I don't think we will need to mix types)
- to "concat" we just need to shift left. More efficient to represent total conditions than with integers? 
  - z3 actually supports a concat operation for bitvector variables
- bitmask op might make it easier to derive variable conditions form experimental conditions
  - does this eliminate the need for additional z3 variables?

#### Benefit of Bitvectors with n bits?
observation: all vectors are orthogonal unit vectors, so this might allow a different way of combining vectors other than concat... however, this would still result in more bits per vectors.  

