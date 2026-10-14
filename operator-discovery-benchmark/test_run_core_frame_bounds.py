"""Source-binding and proof-status preservation for emitted arithmetic goals."""
from copy import deepcopy
import unittest
from prime_bank_candidates import Meter
import core_cutoff_frame as F
import core_frame_bounds as P
import run_core_frame_bounds as R

M = Meter(10000000, 180)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_run_core_frame_bounds operations='+str(M.operations))


class FrameBoundRunnerTests(unittest.TestCase):
    def setUp(self):
        self.catalogue = F.catalogue(2, M)
        self.certificates = P.synthesize(self.catalogue, M)['certificates']
        self.parent = dict(generated_bound_constructions=[dict(candidate_id=0, whole_signed_bound_proved=False,
            source_binding_ids=['channel_a', 'channel_b'])])
        self.representations = [dict(geometry_id=i, alpha='1/3', gamma=gamma,
            bindings=[dict(parent_obligation_id='channel_a'), dict(parent_obligation_id='channel_b')],
            drift=dict(theta='2/3', polynomial=[dict(powers=[1, 0, 0, 0], coefficient='1'),
                                               dict(powers=[0, 1, 0, 0], coefficient='-1')]))
            for i, gamma in enumerate(('1/3', '2/3'))]
        self.conditions = P.source_conditions(self.representations, self.certificates, M)

    def test_every_original_channel_and_signed_goal_remain(self):
        output = R.compile_feedback(self.parent, self.certificates, self.representations, self.conditions)[0]
        self.assertEqual(output['parent_construction'], self.parent['generated_bound_constructions'][0])
        self.assertEqual(len(output['source_representations']), 2)
        for source in output['source_representations']:
            self.assertEqual(source['all_source_binding_ids'], ['channel_a', 'channel_b'])
        self.assertFalse(output['whole_signed_bound_proved'])
        self.assertFalse(output['actual_moment_condition']['arithmetic_inequality_proved'])
        self.assertEqual(output['search_feedback']['equivalent_rewrite_credit'], 0)

    def test_omitted_or_duplicated_source_binding_is_rejected(self):
        for duplicate in (False, True):
            bad = deepcopy(self.representations)
            if duplicate: bad[0]['bindings'][1] = bad[0]['bindings'][0]
            else: bad[0]['bindings'].pop()
            with self.assertRaises(ValueError): R.compile_feedback(self.parent, self.certificates, bad, self.conditions)

    def test_algebraic_proof_does_not_promote_arithmetic_condition(self):
        bad = deepcopy(self.conditions)
        bad[0]['arithmetic_inequality_proved'] = True
        with self.assertRaises(ValueError): R.compile_feedback(self.parent, self.certificates, self.representations, bad)
        with self.assertRaises(ValueError): R.compile_feedback(self.parent, self.certificates, self.representations, [])


if __name__ == '__main__':
    unittest.main()
