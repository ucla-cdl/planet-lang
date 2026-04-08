from planet import *
from planet.analysis import Analysis

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
        .absolute_rank(drug, "placebo", 1)
        .within_subjects(diet)
        .absolute_rank(diet, "healthy", 1)
)

print(assign(units, design))
print(Analysis(design))


