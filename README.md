# PLanet
Welcome to the PLanet repository. PLanet is a high-level, declarative
programming language to help researchers author verifiable experimental designs.

If installing from source, install the requirements using `pip3 install -r
requirements.txt` to setup the environment.
Source files are located in `src/planet`. Example programs are
located in `src/examples` and `src/eval_examples`. Outputs from the program
(such as the latex table or csv file) are located in `/outputs` within the
working directory. 


# PLanet
Welcome to PLanet's documentation! PLanet is a tool to help researchers author and analyze experimental designs.

# Effect Types 
Below, we provide brief definitions and examples for different effects in an
experiment. PLanet's analysis identifies which effects you can test in an
experiment and whether they are influenced by other factors. 

  ### Main Effects
  The independent influence of a single variable on the outcome, averaged across all levels of any other variables.

    ex: The influence of interface on task time regardless of task type is the main effect of the interface.

### Interaction Effects 
   The influence of a variable that depends on the level (i.e., condition) of
   another variable. When interaction effects exist, main effects alone can be
   misleading and should be interpreted with caution.
   
    ex: If VR only outperforms baseline on the "run" task but not others, that is an interface × task interaction.

### Time-Based Effects
The influence of time or state over the course of an experiment. PLanet
indicates which effects can be interpreted without bias from time-based
effects.

      ex: 'Learning effects are one example of time-based effects where participants perform better in later trials, simply because they learned more about the task over the course of the study.

# Constructs 
## Experiment Variable
An Experiment Variable is an independent variable the experimenter wants to use in an experiment. The experiment variables included in an experiment determine the conditions a unit sees. For example, treatment is an Experiment Variable with two conditions: drug or placebo. 

<img src="tutorial/img/var-ui.png" alt="alt text" width="300">

```python
Variable(name, options=[])
```
Creates an experimental variable. 

Parameters:

 - `name: str` -- name of the variable. 
 - `options: str[]` -- list of possible discrete assignment values of the variable. 


## Design
A design consists of every possible experimental plan a unit can get assigned
to, and the method of assigning these experimental plans to units. Experimental
designs describe the method of assigning conditions to units in an experiment. 

<img src="tutorial/img/design-ui.png" alt="alt text" width="300">

```python
Design()
```
Creates an experimental design object. 


## Operations
### BS
Adds a between subjects variable to the design. Adding a between-subjects
variable implies the assignment value to the between-subjects variable is the
same across all trials within a participant. 

<img src="tutorial/img/bs-ui.png" alt="alt text" width="300">

```python
( 
    Design()
    .between_subjects(variable)
)
```

Parameters:

 - `variable: ExperimentVariable` -- an experiment variable. 


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])

design = (
    Design()
    .between_subjects(treatment)
)
```
Creates a design with exactly one between-subjects variable, treatment. 

### WS
Adds a within subjects variable to the design. Adding a within subjects implies that assigment value to the within-subjects variable is the different for every trial in each experiment plan. 

<img src="tutorial/img/cb-ui.png" alt="alt text" width="300">

```python
( 
    Design()
    .within_subjects(variable)
)
```

Parameters:

 - `variable: ExperimentVariable` -- an experiment variable. 


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])

design = (
    Design()
    .within_subjects(treatment)
)
```
Creates a design with exactly one between-subjects variable, treatment. 

### CB
Counterbalances the specified variables, meaning we observe each variable value
an equal number of times in each position across all plans. 
Then input variable must already be specified in the
design as either within or between subjects.

<img src="tutorial/img/cb-ui.png" alt="alt text" width="300">

```python
( 
    Design()
    .within_subjects(variable)
    .counterbalance(variable)
)
```
Parameters:

 - `variable: ExperimentVariable` -- an experiment variable. 


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])

design = (
    Design()
    .within_subjects(treatment)
    .counterbalance(treatment)
)
```
Creates a design with treatment as a within-subjects with counterbalanced
conditions, treatment. The result of this program is a fully-counterbalanced
design with two possible experiment plans: $drug \rightarrow placebo$ and $placebo \rightarrow drug$.

### limit plans
Limits the number of unique plans in the design. Limit plans set a maximum limit
on the number of assigned orders in an experimental design. 

<img src="tutorial/img/limit-plans-ui.png" alt="alt text" width="300">

```python
( 
    Design()
    .limit_plans(n)
)
```

Parameters:

 - `n: int` -- the exact number of plans in the design. 

Returns: A `Design` object


### Example
```python
treatment = Variable("treatment", options=["drug", "drug2", "placebo"])

design = (
    Design()
    .within_subjects(treatment)
    .counterbalance(treatment)
    .limit_plans(len(treatment))
)
```

The result is a counterbalanced, within-subjects design with three plans.
Because there are three assignment values of the treatment variable, each
treatment condition appears exactly once in each position.
If we do not limit the number of
plans, there are six possible orders, resulting in a fully-counterbalanced
design. 


Sets the number of trials for each plan in the design. 

```python
( 
    Design()
    .num_trials(n)
)
```

Parameters:

 - `n: int` -- the exact number of trials in each experimental plan.  -->


```python
treatment = Variable("treatment", options=["drug", "drug2", "placebo"])

design = (
    Design()
    .within_subjects(treatment)
    .counterbalance(treatment)
    .num_trials(2)
)
```

### order
Sets a fixed order of conditions. 
Requires that all conditions of a variable are specified in the order at least
once. 

<img src="tutorial/img/order-ui.png" alt="alt text" width="300">

```python
( 
    Design()
    .order(variable, ordering)
)
```

Parameters:
 - `variabe: ExperimentVariable` -- an experiment variable. 
  - `ordering: []str` -- list of conditions.

### Example
```python
treatment = Variable("treatment", options=["a", "b"])

design = (
    Design()
    .within_subjects(treatment)
    .order(variable, ["b", "a"])
)
```

This results in a design with exactly one order ($a \rightarrow b$) 

## Composing Designs
### nest
Composes orders of two designs as one design with a nesting strategy. Nesting ensures
that every condition of each order in the *inner* design is nested within each
trial of the *outer* design. 

<img src="tutorial/img/nest.png" alt="alt text" width="600">

<img src="tutorial/img/nest-ui.png" alt="alt text" width="300">

```python
nest(inner=design1, outer=design2)
```
Parameters:

- `outer: Design` -- a design. 
-  `inner: Design` -- a design. 

### Example
```python

treatment = ExperimentVariable( 
    name = "treatment",
    options = ["drug", "placebo"]
)
task = ExperimentVariable(
    name = "task",
    options = ["run", "walk"]
)

treatment_des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
)

task_des = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)

des = nest(inner=treatment_des, outer=task_des)
```

### cross
Composes orders of two designs into one design with a crossing strategy. Crossing ensures
that each order in the first design is overlaid with each order of the second
design. `cross` requires that each design has the same number of trials per
participant. 

<img src="tutorial/img/cross-ui.png" alt="alt text" width="300">

```python
cross(design1, design2)
```

<img src="tutorial/img/cross.png" alt="alt text" width="600">

Parameters:

- `design1: Design` -- a design 
-  `design2: Design` -- a design


### Example
```python

treatment = ExperimentVariable( 
    name = "treatment",
    options = ["drug", "placebo"]
)
task = ExperimentVariable(
    name = "task",
    options = ["run", "walk"]
)

treatment_des = (
    Design()
        .within_subjects(treatment)
        .counterbalance(treatment)
)

task_des = (
    Design()
        .within_subjects(task)
        .counterbalance(task)
)

des = cross(treatment_des, task_des)
```

### multifact
Combines every condition of all sub-variables to create a new variable, where
the conditions are the combined conditions of its sub-variables. 

<img src="tutorial/img/mv-ui.png" alt="alt text" width="300">

```python
multifact(variables[])
```

Parameters:

- `variables: ExperimentVariable[]` -- a list of experiment variables


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])
task = Variable("task", options=["run", "walk"])

multi_fact_variable = multifact([treatment, task])
```

The result is a new variable, treatment-task. The possible conditions are the
combined conditions from each variable (e.g., drug-run, placebo-run, drug-walk,
placebo-walk). 



