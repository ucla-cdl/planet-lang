from planet import *

pesonalization = ExperimentVariable("personalization", options=["in_app_demographic", "in_app_content", "in_app_collaborative", "social_media_demographic", "social media content", "social media collaborative"])
user_choice = ExperimentVariable("choice", options=["present", "absent"])

participants = Units(341)

design = (
    Design()
    .between_subjects(multifact([pesonalization, user_choice]))
)

print(assign(participants, design))
