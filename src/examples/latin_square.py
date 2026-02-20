from planet import *


"""
an experiment testing the effects of AR and VR interfaces compared to a
real-world scenario.
"""

drug = ExperimentVariable(
    name = "drug",
    options = ["tylenol", "placebo"]
)

diet = ExperimentVariable("diet", options = ["unhealthy", "healthy"])

units = Units(8)

design = (
    Design()
        .within_subjects(drug)
        .counterbalance(drug)
        .within_subjects(diet)
        .counterbalance(diet)
)

print(assign(units, design))


