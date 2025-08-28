# PLanet
Welcome to the PLanet repository. PLanet is a high-level, declarative
programming language to help researchers author verifiable experimental designs.


To set up the environment, install the requirements using `pip3 install -r requirements.txt`. 
Source files are located in `src/lib`. Example programs are
located in `src/examples` and `src/eval_examples`. Outputs from the program
(such as the latex table or csv file) are located in `src/outputs`. 


# Objects 
## Units
```python
Units(n)
```

A sample of n units (often participants) selected to participate in an experiment. 

Parameters:

 - `n: int` -- the number of units in the sample. For example, if we want to sample 25 participants, then n = 25. Each participant represents one unit. If unspecified, n defaults to the minimum number of units necessary for a valid experimental design. 
  
## Experiment Variable
An Experiment Variable is an independent variable or covariate the experimenter wants to use in an experiment. The experiment variables included in an experiment determine the conditions a unit sees. For example, treatment is an independent variable with two values: drug or placebo. 

```python
Variable(name, options=[])
```
Creates an experimental variable. 

Parameters:

 - `name: str` -- name of the variable. 
 - `options: str[]` -- list of possible discrete assignment values of the variable. 

Returns: A `Variable` object

## Design
A design consists of every possible experimental plan a unit can get assigned
to, and the method of assigning these experimental plans to units. Experimental
designs describe the method of assigning conditions to units in an experiment. 

```python
Design()
```
Creates an experimental design object. 
Returns: A `Design` object

## Replications
Replications are a special design that assign arbitrary or empty trials to units.
Replications combined with Designs to form create designs with replicated
conditions. For example, n replications results in n occurances of
each condition of the experimental variables within each participant. 

```python
Replications(int)
```
Creates a replications object. 
Returns: A `Replications` object

### Example use case
```python
task = ExperimentVariable("task", options=["a", "b"])

design = (Design()
        .within_subjects(task)
)

nest(inner=Replications(2), outer=design)
```

### Example output
| Participant | Trial | task |
| ----------- | ----- | ---- |
| P1          | T1    | a    |
| P1          | T2    | a    |
| P1          | T3    | b    |
| P1          | T4    | b    |
| P2          | T1    | b    |
| P2          | T2    | b    |
| P2          | T3    | a    |
| P2          | T4    | a    |



## Methods
### between_subjects
Adds a between subjects variable to the design. Adding a between-subjects variable implies the assigment value to the between-subjects variable is the same throughout every trial in each experiment plan. 

```python
( 
    Design()
    .between_subjects(variable)
)
```

Parameters:

 - `variable: Variable` -- an experiment variable. 

Returns: A `Design` object


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])

design = (
    Design()
    .between_subjects(treatment)
)
```
Creates a design with exactly one between-subjects variable, treatment. 

### within_subjects
Adds a within subjects variable to the design. Adding a within subjects implies that assigment value to the within-subjects variable is the different for every trial in each experiment plan. 

```python
( 
    Design()
    .within_subjects(variable)
)
```

Parameters:

 - `variable: Variable` -- an experiment variable. 

Returns: A `Design` object


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])

design = (
    Design()
    .within_subjects(treatment)
)
```
Creates a design with exactly one between-subjects variable, treatment. 

### counterbalance
Counterbalances the specificed variables, meaning we observe each variable value an equal number of times for each trial number accross all plans. During assignment, an equal number of units get assigned to each variable assignment value at each trial number. Assumes the input variable has already been specified in the design as either within or between subjects.

```python
( 
    Design()
    .within_subjects(variable)
    .counterbalance(variable)
)
```
Parameters:

 - `variable: Variable` -- an experiment variable. 

Returns: A `Design` object


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])

design = (
    Design()
    .within_subjects(treatment)
    .counterbalance(treatment)
)
```
Creates a design with exactly one within-subjects, counterbalanced variable, treatment. The result of this program is a fully-counterbalanced design with two possible experiment plans: drug -> placebo and placebo -> drug. An equal number of units get assigned to each plan during assignment. 

### limit_plans
Limits the number of unique plans in the design. This acts as a constraint that prunes the space of all possible plans. 

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

The result is a counterbalanced, within-subjects design with three plans. Because there are three assignment values of the treatment variable, and we limit the number of plans to the number of assignment values, the result is a latin square. By default, the number of plans is the maximum number of plans given the description of the design. If we do not limit the number of plans, there are six possible orders, resulting in a fully-counterbalanced design. 

### num_trials
Sets the number of trials for each plan in the design. 

```python
( 
    Design()
    .num_trials(n)
)
```

Parameters:

 - `n: int` -- the exact number of trials in each experimental plan. 

Returns: A `Design` object

### Example
```python
treatment = Variable("treatment", options=["drug", "drug2", "placebo"])

design = (
    Design()
    .within_subjects(treatment)
    .counterbalance(treatment)
    .num_trials(2)
)
```

The result is a fully-counterbalanced, within-subjects design, where each units
gets observed twice. This means that not every unit sees every assignment value
of the treatment variable. The number of plans 3!/1! = 6. 

### set_rank
Sets presedence of a variable's order accross all plans. Default rank is 0.
Setting a higher rank to one condition results in this condition preceeding all
other conditions. 

```python
( 
    Design()
    .set_rank(variable, condition, rank)
)
```

Parameters:
 - `variabe: ExperimentVariable` -- an experiment variable. 
  - `condition: str` -- name of condition corresponding to experiment variable. 
 - `n: int` -- integer indicating rank of condition in order. 

Returns: A `Design` object

### Example
```python
treatment = Variable("treatment", options=["a", "b"])

design = (
    Design()
    .within_subjects(treatment)
    .set_rank(treatment, "a", 1)
)
```

This results in one viable order: [a, b] because a (rank: 1) must always appears
before b (rank: 0) in any order. 


### to_latex()
Creates a file called design.tex in an folder called outputs. The design.tex
file contains latex code for displaying a table representing the design. 

```python
Design().to_latex()
```


### Example Output
```latex
\begin{tabular}{lllll}
\toprule
 & trial1 & trial2 & trial3 & trial4 \\
\midrule
0 & basketball-VR & painting-VR & basketball-baseline & painting-baseline \\
1 & painting-VR & basketball-VR & painting-baseline & basketball-baseline \\
2 & basketball-baseline & painting-baseline & basketball-VR & painting-VR \\
3 & painting-baseline & basketball-baseline & painting-VR & basketball-VR \\
\bottomrule
\end{tabular}
```

## Combining Designs

### nest
Combines two designs into one with a nesting strategy, meaning that within every trial of the outer design, we observe every trial of the secodn design. The overall condition is now the combination of conditions assigned in each of the sub-designs. 

An experimenter may use a nested design when they need to counterbalance a multifactorial design, and they have assumptions about how the values of some variable may effect a unit when completing a future task.  


```python
nest(outer_design, inner_design)
```

Parameters:

- `outer: Design` -- a design used as the outer design in a new design. The trials of trials in the outer design expand to account for the trials of the plans in the inner design. 
-  `inner: Design` -- a design used as the inner design in a new design. All of the plans in the inner design are replicated by the number of trials in all of the plans in the outer design. 

Returns: A `Design` object


### Example
```python
# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
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

des = nest(treatment_des, task_des)
```

### cross
Combines two designs into one with a crossed strategy, meaning that every plan in the first design superimposes with every plan in the second design. Compared to nest, the number of trials do not increase, so the number of trials must be the same for each sub-design. The number of plans in the new design is n by m, where n is the number of plans in the first design, and m is the number of plans in the second design. 

Cross is useful when the unit does not need to complete every combination of conditions in a multifactorial design, but it is important for them to see every condition of every variable involved in the design. 
```python
cross(design1, design2)
```

Parameters:

- `design1: Design` -- a design used to create a new design 
-  `design2: Design` -- a design used to create a new design

Returns: A `Design` object


### Example
```python
# user creates two variables: task and treatment 
# the user provides the variable name, and an array 
# of the possible conditions for the variable
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
Combines every condition of all input-variables to create a multi-factor variable. 

```python
multifact(variables[])
```

Parameters:

- `variables: Variable[]` -- a list of experiment variables

Returns: A `MultiFactVariable` object


### Example
```python
treatment = Variable("treatment", options=["drug", "placebo"])
task = Variable("task", options=["run", "walk"])

multi_fact_variable = multifact(treatment, task)
```

### This is similar to manually combining the variables, but using multifact keeps references of the variables it is composed of. 

```python
multi_fact_variable = Variable("treatment_task", options=["drug-walk", "placebo-walk", "drug-run", "placebo-walk"])
```

### assign
Randomly matches units to plans based on the strategy specified in the design.
Every unit is assigned exactly one plan. The same plan can be assigned to
multiple units. 

```python
assign(units, design)
```

Parameters:

- `units: Units` -- a sample of units to which we want to assign an experiment plan
-  `design: Design` -- a design specifying how conditions are assigned to unit. 

Returns: An `Assignment` object

### to_csv()
Creates a csv file in a folder called outputs. The 
file contains a csv file with a row for every unit. The first column contains a
unit id, and there are n additional columns for every trial in the experiment
plan.  

```python
assign(units, design).to_csv()
```

