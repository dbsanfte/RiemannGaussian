import copy
import unittest

import mobius_prime_storage_feedback_073 as F


def candidate(theta, direction, q='1', weight='1'):
    return dict(schema='signed-prime-storage-candidate-v1',spec=dict(profile=F.PROFILE,theta=theta),
                labels=F.BASE_LABELS+['smooth:'+t for t in theta],q=q,
                rays=[dict(weight=weight,direction=direction)])


class ProofFeedbackTests(unittest.TestCase):
    def test_registered_smooth_bulk_rejects_every_constant(self):
        c=candidate(['2/3','4/5'],['0']*6+['1/4','-1/8'],weight='3/7')
        r=F.analyze(c)
        self.assertEqual(r['status'],'REFUTED_FOR_EVERY_FINITE_DRIFT_CONSTANT')
        self.assertEqual(r['rays'][0]['liminf_energy_coefficient'],'3/112')
        self.assertTrue(r['rays'][0]['any_finite_base_extension_excluded'])

    def test_unknown_mode_not_silently_dropped(self):
        c=candidate(['3/7','2/3'],['0']*6+['1','1'])
        self.assertEqual(F.analyze(c)['status'],'NO_EXCLUSION_BY_REGISTERED_MODES')

    def test_exact_centering_is_not_a_recurrence_proof(self):
        c=candidate(['2/3','4/5'],['1','0','2','2','2','2','1','-1'])
        r=F.analyze(c)
        self.assertFalse(r['uniform_recurrence_proved'])
        self.assertEqual(r['rays'][0]['effective_target_coefficient'],'3')
        self.assertEqual(r['status'],'NO_EXCLUSION_BY_REGISTERED_MODES')

    def test_first_order_sector_dominates_all_smooth_coordinates(self):
        c=candidate(['2/7'],['0','0','0','0','1','0','-100'])
        r=F.analyze(c)['rays'][0]
        self.assertEqual(r['status'],'FIXED_FACTOR_COUNT_BULK')
        self.assertEqual(r['loglog_numerator_power'],4)
        self.assertEqual(r['leading_coefficient'],'1')

    def test_power_gate_and_source_binding(self):
        c=candidate(['2/3'],['0']*6+['1'],q='2')
        self.assertEqual(F.analyze(c)['status'],'NO_EXCLUSION_BY_REGISTERED_MODES')
        bad=copy.deepcopy(c);bad['spec']['profile'][0][0]='7'
        with self.assertRaises(ValueError):F.analyze(bad)
        bad=copy.deepcopy(c);bad['rays'][0]['weight']='-1'
        with self.assertRaises(ValueError):F.analyze(bad)


if __name__=='__main__':unittest.main()
