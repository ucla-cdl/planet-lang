Welcome! This is a tutorial for PLanet. We will walk through examples defining
experimental designs using PLanet. [file] constains started code
that you will fill-in alongside this tutorial. Let's begin!

Before constructing a design, we need to know which variables are important in
the experiment. ExperimentVariables in PLanet are the independent and control
variables in your experiment. 

```python
interface = ExperimentVariable("interface", options=["baseline", "VR", "AR"])
```

Now that we've defined a variable, we can start composing a design. The most
basic design in PLanet is a between-subjects design with one experiment
variable. First, let's instantiate a *Design*:

```python
design = (
    Design()
)
```

Great! To include our variable in the design, we should specify whether it is a
between-subjects or within-subjects variable: 


```python
design = (
    Design()
        .between_subjects(interface)
)
```

Between-subjects designs assign one condition to each unit. We can run our
result by running the assignment procedure based on the design. To do this, we
need to identify units. Let's say we recruited 12 participants:

```python
units = Units(12)
```

Now, let's assign the interface to the 12 units using our design:

```python
assign(units, design)
```

We can also create a within-subjects design, meaning each participant recieves
more than one condition: 

```python
design = (
    Design()
        .within_subjects(interface)
)
```

By default, the design assigns every condition to each unit. We can define a
design where we assign two conditions to each unit and there are three
conditions: 

```python
design = (
    Design()
        .within_subjects(interface)
        .num_trials(2)
)
```

Right now, the orders are completely random. Run your program and observe the
output. Notice that there is a plan for every unit. Your output should look
similar to this:


```bash
...
plan 10:
	trial 1: interface = AR
	trial 2: interface = baseline
plan 11:
	trial 1: interface = AR
	trial 2: interface = baseline
plan 12:
	trial 1: interface = baseline
	trial 2: interface = AR
 

***ASSIGNMENT***

    pid  plan
0     1     2
1     2     8
2     3    11
3     4     3
4     5     0
5     6     4
6     7     7
7     8     9
8     9     6
9    10    10
10   11     5
11   12     1
```

Theoretically, there is a chance
that we assign every unit the same order! Counterbalancing prevents this by
enforcing that every condition appears an equal number of times. 

```python
design = (
    Design()
        .within_subjects(interface)
        .num_trials(2)
        .counterbalance(interface)
)
```

### Possible Output 
```bash
***EXPERIMENT PLANS***

plan 1:
	trial 1: interface = AR
	trial 2: interface = baseline
plan 2:
	trial 1: interface = AR
	trial 2: interface = VR
plan 3:
	trial 1: interface = baseline
	trial 2: interface = VR
plan 4:
	trial 1: interface = baseline
	trial 2: interface = AR
plan 5:
	trial 1: interface = VR
	trial 2: interface = baseline
plan 6:
	trial 1: interface = VR
	trial 2: interface = AR
 

***ASSIGNMENT***

    pid  plan
0     1     5
1     2     4
2     3     4
3     4     5
4     5     2
5     6     3
6     7     3
7     8     0
8     9     2
9    10     1
10   11     1
11   12     0
```

There are six possible orders for this design, and the same number of
participants are assigned to each order! This ensures that we observe every
condition at every position of the order an equal number of times. 

Now, let's design a Latin square for a new variable. 

```python
task = ExperimentVariable(
    name = "task",
    options=["run", "walk", "sprint"]
)
```
```python
task_design = (
    Design()
    .within_subjects(task)
)
```

Latin sqaures are a particular instance of counterbalanced desings, where every
condition appears once at every position of the order. 

```
a b c
b c a
c a b
```

Let's see what happens when we counterbalanced the task conditions

```python
task_design = (
    Design()
    .within_subjects(task)
    .counterbalance(task)
)
```

```python
assign(units, task_design)
```

This results six possible orders, but, for a degree three Latin square, there are only
three orders! We need to limit the number of plans.

```python
task_design = (
    Design()
    .within_subjects(task)
    .counterbalance(task)
    .limit_plans(len(task))
)
```
```bash
***EXPERIMENT PLANS***

plan 1:
	trial 1: task = walk
	trial 2: task = sprint
	trial 3: task = run
plan 2:
	trial 1: task = sprint
	trial 2: task = run
	trial 3: task = walk
plan 3:
	trial 1: task = run
	trial 2: task = walk
	trial 3: task = sprint
 

***ASSIGNMENT***

    pid  plan
0     1     1
1     2     1
2     3     2
3     4     2
4     5     0
5     6     1
6     7     0
7     8     2
8     9     0
9    10     2
10   11     0
11   12     1
```

Now, there are three plans, and each of the thee conditions appear first,
second, and third once. 

We can also combine the designs by nesting them.

```python
design = nest(inner=task_design, outer=interface_design)
assign(units, design)
```

```bash
...
plan 17:
	trial 1: task = run, interface = VR
	trial 2: task = sprint, interface = VR
	trial 3: task = walk, interface = VR
	trial 4: task = run, interface = AR
	trial 5: task = sprint, interface = AR
	trial 6: task = walk, interface = AR
plan 18:
	trial 1: task = walk, interface = VR
	trial 2: task = run, interface = VR
	trial 3: task = sprint, interface = VR
	trial 4: task = walk, interface = AR
	trial 5: task = run, interface = AR
	trial 6: task = sprint, interface = AR
 

***ASSIGNMENT***

    pid  plan
0     1     4
1     2     9
2     3     3
3     4    15
4     5    17
5     6     1
6     7     7
7     8     6
8     9    14
9    10     8
10   11     0
11   12    13
12   -1     2
13   -1     5
14   -1    12
15   -1    10
16   -1    16
17   -1    11
```

When nesting these designs, we need 18 participants to satisfy our
counterbalancing properties. The table sets PID to $-1$ to reflect *dropouts*.
This suggests that we should recruit more participants. 

Let's modify the first design, so we always start with the baseline. 

Now, every plan starts with the baseline condition. 

```bash
...
plan 3:
	trial 1: task = walk, interface = baseline
	trial 2: task = sprint, interface = baseline
	trial 3: task = run, interface = baseline
	trial 4: task = walk, interface = VR
	trial 5: task = sprint, interface = VR
	trial 6: task = run, interface = VR
	trial 7: task = walk, interface = AR
	trial 8: task = sprint, interface = AR
	trial 9: task = run, interface = AR
plan 4:
	trial 1: task = sprint, interface = baseline
	trial 2: task = run, interface = baseline
	trial 3: task = walk, interface = baseline
	trial 4: task = sprint, interface = AR
	trial 5: task = run, interface = AR
	trial 6: task = walk, interface = AR
	trial 7: task = sprint, interface = VR
	trial 8: task = run, interface = VR
	trial 9: task = walk, interface = VR
...
```

Now that you're familiar with PLanet's core features, try authoring your own experimental design from scratch using the starter code! Don't worry if you didn't remember everything.
You can always reference the tutorial again. 