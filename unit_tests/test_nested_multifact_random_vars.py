"""Components of a composed multifactor variable are not free random variables."""
import unittest

from planet import Design, ExperimentVariable, Units, assign, cross, multifact, nest


def variable(name, levels):
    return ExperimentVariable(name=name, options=[str(i) for i in range(levels)])


def nested_multifact(counterbalanced):
    """A multifactor within-subjects design repeated in three blocks."""
    grains = ExperimentVariable("Number of Grains", options=["9", "19", "39"])
    electrodes = ExperimentVariable("Electrode Conditions", options=["0", "4", "6", "9"])
    joint = multifact([grains, electrodes])
    inner = Design().within_subjects(joint)
    if counterbalanced:
        inner.counterbalance(joint).limit_plans(len(joint))
    return joint, nest(outer=Design().num_trials(3), inner=inner)


class NestedMultifactRandomVariables(unittest.TestCase):
    def assert_blocks_permute(self, plans, joint, index=slice(None)):
        """Every consecutive block of a plan holds each joint condition once."""
        width = len(joint)
        for plan in plans:
            self.assertEqual(len(plan) % width, 0)
            for start in range(0, len(plan), width):
                block = ["-".join(cell.split("-")[index]) for cell in plan[start:start + width]]
                self.assertEqual(set(block), set(joint.conditions))


    def test_counterbalanced_components_are_not_random(self):
        joint, design = nested_multifact(counterbalanced=True)
        # The joint variable is counterbalanced; its components only carry
        # the block constraints added by nesting, which does not free them.
        self.assertEqual(design.identify_random_vars(), [])
        plans = [list(plan) for plan in assign(Units(12), design).computed_plans]
        self.assertEqual(len(plans), 12)
        self.assertEqual({len(plan) for plan in plans}, {36})
        self.assert_blocks_permute(plans, joint)
        # Each plan repeats its own block order three times, and the plans
        # counterbalance the joint conditions across every trial position.
        for plan in plans:
            self.assertEqual(plan[:12], plan[12:24])
            self.assertEqual(plan[:12], plan[24:])
        for trial in range(12):
            self.assertEqual({plan[trial] for plan in plans}, set(joint.conditions))


    def test_random_multifact_is_randomized_as_one_variable(self):
        joint, design = nested_multifact(counterbalanced=False)
        self.assertEqual(design.identify_random_vars(), [joint])
        plans = assign(Units(4), design).computed_plans
        self.assertEqual(len(plans), 4)
        self.assertEqual({len(plan) for plan in plans}, {36})
        # The joint variable is shuffled within each block of twelve, not
        # across the whole plan of 36 trials.
        self.assert_blocks_permute(plans, joint)
        blocks = {tuple(plan[start:start + 12]) for plan in plans for start in (0, 12, 24)}
        self.assertGreater(len(blocks), 1)


    def test_crossed_multifact_components_are_not_random(self):
        a, b, c = variable("a", 2), variable("b", 2), variable("c", 4)
        joint = multifact([a, b])
        first = Design().within_subjects(joint).counterbalance(joint).limit_plans(4)
        second = Design().within_subjects(c).counterbalance(c).limit_plans(4)
        design = cross(first, second)
        self.assertEqual(design.identify_random_vars(), [])
        plans = assign(Units(16), design).computed_plans
        self.assertEqual(len(plans), 16)
        self.assertEqual({len(plan) for plan in plans}, {4})
        self.assert_blocks_permute(plans, joint, index=slice(0, 2))
