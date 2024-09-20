# NEXT STEPS: 
- Organize List of desirables: group, filter, prioritize

Overall approach: Start with assignment and measurement, others as "black boxes" 
    - Start with multiple black boxes and then over time specify more and more of them / open them up

# List of desirable language features/constructs
- Distinction between experiment vs. real-world: What were pragmatic decisions made for the sake of measurement vs. how these quantities/constructs arise in the world? (Derived data vs. fundamental data)
    - Derivation of proxies 
- Explicit hierarchies of measurement/proxies
- Clear sense of intervention
- Support comparing of experiments
- Support merging of experiments across a full body of conclusions
- Capture participant behavior
- Participant recruitment
- Causal relationships between variables and others not measured
- Inference algorithm
- Capture temporal aspect of experiments: There is a notion of linear progression 

- would like to explain common ED jargon: within-subjects, between-subjects, nesting -> These should be syntactic sugar
- Flexibility: Can change “views” for considering experiment from perspective of per trial vs. per observational unit – similarly, what would it be like to specify an experiment from the perspective of aggregating across participants vs. each participant; is there a difference? **Is this a program analysis?**
- Separate out design (e.g., set of trials, see one of each) from quantification (e.g., number of conditions or trials) -- Analogies to other programming paradigms? Domains?

- separate experimental design decision (allocation of observations/samples) from statistical representation (e.g., interaction effect) from data simulation
- separate variable properties (e.g., distribution, range) from assignment in experiment
- separate variable from its role in an experiment (e.g. IV, DV, others?)

Currently captured in mind: 
![Experiment as a subset of world with connections between the two](../figures/exp-world.png)
- What would those connections/edges be? 

# Tasks to support
(These are the things that a formal representation of experiments would enable that we can't yet do.)
- Checks on validity within an experiment (Does this by definition have to be internal validity?)
    - Related work: PlanAlyzer
- Is this experiment feasible?
- Infeasible → feasible experiment (compiler optimization)
    - Feasibility wrt set of constraints (boolean, cost function/budget – Rogers and Jamieson multi-armed bandits for experimental design)?
- Simulate data
- Check that experimental design is consistent/compatible with conceptual/causal model of domain
- How to update model of world based on experiment?
- Should be able to discover isomorphic experimental designs: sequence of randomization vs. randomized sequence 
- generate data invariants or checks based on experimental design/data collection procedure


# Broad classes of concern in "experimental design" 
- Assignment, measurement, sampling


# Basic operations in experimental design
- Assignment
- Randomization
- Repetition (loop)
