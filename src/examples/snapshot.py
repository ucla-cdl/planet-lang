from planet import *

interface = ExperimentVariable("interface", options=["baseline", "VR", "AR"])

participants = Units(12)

design = (
    Design()
        .within_subjects(interface) # include interface as argument
        .counterbalance(interface) # include interface as an argument
)

print("TEST", design.trials)
print(assign(participants, design))

design = (design
          .num_trials(2)
)
print(assign(participants, design))