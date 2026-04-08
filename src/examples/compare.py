from planet import *
from planet.analysis import Analysis, compare

"""
an experiment testing the effects of AR and VR interfaces compared to a
real-world scenario.
"""

drug = ExperimentVariable(
    name = "drug",
    options = ["tylenol", "placebo"]
)

units = Units(8)

design1 = (
    Design()
        .within_subjects(drug)
        .counterbalance(drug)
)

design2 = (
    Design()
        .between_subjects(drug)
)

compare(design1, design2)
