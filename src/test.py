import random

def generate_conditions(participants, conditions, trials_per_condition=1):
    """
    Generates a randomized sequence of conditions for each participant.
    
    :param participants: Number of participants
    :param conditions: List of conditions
    :param trials_per_condition: Number of times each condition should appear
    :return: Dictionary mapping participant IDs to their condition sequences
    """
    experiment_data = {}

    for participant in range(1, participants + 1):
        condition_list = conditions * trials_per_condition  # Repeat conditions
        random.shuffle(condition_list)  # Shuffle for randomization
        experiment_data[f"Participant_{participant}"] = condition_list
    
    return experiment_data


