import sys
import os
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../")))

from lib.variable import ExperimentVariable, multifact
from lib.design import Design, nest
from lib.unit import Units 
from lib.assignment import assign 

pesonalization = ExperimentVariable("personalization", options=["in_app_demographic", "in_app_content", "in_app_collaborative", "social_media_demographic", "social media content", "social media collaborative"])
user_choice = ExperimentVariable("choice", options=["present", "absent"])

participants = Units(341)

design = (
    Design()
    .between_subjects(multifact([pesonalization, user_choice]))
)

assign(participants, design)
