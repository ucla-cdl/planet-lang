Last updated: \today

# Defining experiments and their designs

The world is a database with a data schema, $\sigma$. 

The true data schema (i.e., the absolute truths about the world), $\sigma_{true}$, contains information about all the objects in the world and the causal statements between them. These causal statements are the true relations between/among objects in the world. 

Unfortunately, $\sigma_{true}$ is not known completely. 

We do, however, know about the world partially, $\sigma_{partial}$. 

So, $\sigma_{partial} \subset \sigma_{true}$.


The goal of science is to discover $\sigma_{true}$. 

The best way we know how to do that is to probe the world through experiments (e.g., observational studies, RCT, natural experiments, etc), $\chi$. 

An experiment is a set of operations attempting to find and fit a schema using data collected/observed. 

In other words, through an experiment, we want to make a statement such as the following: 

Given $\sigma_{partial}$, if I observe $x$ from conducting experiment $\chi$, that means $\sigma_{true}$ contains the following relations: ....

The $\sigma_{partial}$ scientists think they know might not actually be a subset of the unknowable $\sigma_{true}$. So, scientists need to assume $\sigma_{assumed}$.
There may be a function to transform $\sigma_{partial}$ into  $\sigma_{assumed}$ (and vice versa): 

$f(\sigma_{partial}) = \sigma_{assumed}$. 

So, what we have is 

$f(\sigma_{partial}) \cdot \chi \implies \sigma_{true}$ , which can also be written as

$\sigma_{assumed} \cdot \chi \implies \sigma_{true}$

Notes: 
1. Importantly, scientists may scrutinize and even disagree with the specific $f()$. This means $\sigma_{assumed}$ could be invalid. Any statements about $\sigma_{true}$ from any experiment relying on $\sigma_{assumed}$ needs to be reconsidered/re-evaluated. 
2. The implication ($\implies$) corresponds to statistical analysis. In other words, statistical analysis transforms the left hand side into the right hand side. For simplicity, let's assume that transformation is straightforward and feasible.  
3. This formulation looks a lot like Bayes Theorem, where $\sigma_{assumed}$ and $\sigma_{true}$ correspond (in spirit) to priors and posteriors, respectively.

Furthermore, there are three fundamental concerns of experiments (based on Fisher's Design of Experiments -- I think that's the right citation): measurement, sampling, and assignment. 
The above formulation clarifies that measurement and sampling both map to $\sigma_{assumed}$. Both measurement and sampling are functions transforming $\sigma_{partial}$ into $\sigma_{assumed}$. $\chi$ should capture/is really concerned with assignment. 

The following questions arise: 

- What are the fundamental operations of assignment contained within $\chi$? 

- How can we represent these operations in relational algebra?

- What does $\sigma_{assumed}$ look like? 

- What does $\sigma_{partial}$ look like? 

- How do we formulate any functions (e.g., $f()$) for measurement and sampling that transform $\sigma_{partial}$ into $\sigma_{assumed}$?

Connections to earlier conversations: 

- Users specify their $\sigma_{assumed}$ and $\chi$, which I think correpond to the two things Emery was thinking we could get users to specify
    - $\sigma_{assumed}$ contains the causal assumptions between variables but also facts/assumptions about the variables themselves, including constraints on variable values (as we would expect of any data schema). For example, a statement like "test score can only be positive." These facts should pertain to measurement + sampling. 
    - $\chi$ contains the experimental design as I have been formulating it and writing code examples for. Focused on assignment (including randomization).

- The "world model" is split between $\sigma_{assumed}$ (before experiment) and $\sigma_{true}$ (after experiment). Which makes sense in terms of the fact that the world model should inform an experiment and be updated after an experiment. 
<!-- 
Fall out: 
- The more we know about $\sigma_{partial}$, the more confident/have greater probability that an experiment has established $\sigma_{true}$.

Scraps: 
$\sigma_{assumed}$ contains assumptions about variable data types + relations between the variables.  -->
