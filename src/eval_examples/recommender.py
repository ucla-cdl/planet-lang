from planet import *

"""
https://dl.acm.org/doi/pdf/10.1145/3544548.3581123
"""
pesonalization = ExperimentVariable("personalization", options=["in_app_demographic", "in_app_content", "in_app_collaborative", "social_media_demographic", "social media content", "social media collaborative"])
user_choice = ExperimentVariable("choice", options=["present", "absent"])

participants = Units(341)

design = (
    Design()
    .between_subjects(multifact([pesonalization, user_choice]))
)

print(assign(participants, design))
