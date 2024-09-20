Might be some overlap with previously written [design-goals.md](//experimental-design/design-goals.md)

Scope: Assignment in experimental design (core mechanics of the experiment)

# Definitions (emergent)
Experiment: a set of participants, their assigned tasks (ordered), their assigned conditions (ordered), and observations for each ordered (task, condition) pair
    - Implementation ideas: 
        - "ExperimentTemplate": a set of tasks and conditions that can be assigned
        - "ConcreteExperiment"
        - run(exp) returns a ConcreteExperiment instance (?)

## Necsseary language constructs for assignment 
- Condition
- Task
- Trial :- (index, Task, Condition)
    - Corresponds to two key actions for a participant in each trial of an experiment: 
        - expose to Condition
        - complete Task
- Experiment
- Unit (ID)
- not sure about: distributions from which observations come? -- could this be somethiing we infer/pick defaults for users?

# Programming paradigm (?) => How do we enforce, design this in more???
Current: 
- Declare tasks possible across all participants
- Declare conditions possible across all participants
- Specify how these tasks and conditions can be combined, how they should be ordered for an individual participant

Earlier idea: 
- Declare properties across participants
- Assert properties across participants

# Design choices
General: What does each object/class contain?
    - Experiment: Trials, conditions, other things???

# Technical challenges to address
1. There are rules that are implicit in how researchers order trials, etc. that we capture explicitly
    For Wu et al. UIST 2023: 
    Rules that need to be encoded: 
    - both (all) creation first then both (all) editing
    - every other task has the same condition (i.e., ffl or latex)

2. What are the implicit ordering rules? 
    - We provide preloaded primitives that are common: alternate, sequence random; future work: custom

3. How do we represent these ordering rules?
    - Current idea: Boolean constraints?

4. There might be multiple different kinds of groupings for tasks/conditions. 
    - We allow for a single task/condition to be part of multiple TaskGroups => DO WE WANT TO SUPPORT CONDITION GROUP????

5. Need to specify what comprises a valid trial in an experiment.

# Use cases
## Experiments with validity concerns might be awkward to write in this DSL?

## Possibilities: Input, Output
Input: Program | Output: Text to include in methods section 
Input: Text from methods section | Output: Program 
Input: Program | Output: validity checklist + flags -- does this need mechanized proofs?
Where Input=Program, the Output can  be directed based on different verbs in the API

===
# Out of scope for now: 
- CD++
    - Want to be able to get data for different causal diagrams
    - Maybe the function signatures would be helpful for determining what causal diagrams are feasible + language constructs
- Causal diagram to experimental design compilation
- Causal relationships: Explanations for how the data may arise due to variables in and out of the experiment (World into Experiment)
- *Question*, related to the above point: What if there are causal relationships or more intricate details of experimental tasks that should be reasoned about in order to guarantee validity?
- Execution details: The construction of specific stimuli, questionnaires, and response collection platforms. Services provided about JSPsych, Qualtrics, etc. Note: You can imagine being able to compile our DSL into these execution details for a specific platform.