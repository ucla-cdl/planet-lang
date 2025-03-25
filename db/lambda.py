import random

# Total units and number of treatments
total_units = 24
num_treatments = 4

def randomize():
    # Initialize a list to store the units assigned to each treatment
    treatments = [0] * num_treatments
    units = [0] * total_units

    # Randomly assign 24 units to the treatments
    for i in range(total_units):
        # Choose a random treatment index and assign one unit to it
        treatment_index = random.randint(0, num_treatments - 1)
        units[i] = treatment_index
        treatments[treatment_index] += 1

    # Display the results
    for i, n_units in enumerate(treatments, start=1):
        print(f"Treatment {i} has {n_units} units")

    print(units)

randomize()

if units.has_attribute("hospital1"):
    return "morning-morning-homogenous"