from fractions import Fraction as Q
import unittest

import mobius_prime_storage_073 as S
import check_mobius_prime_storage_073 as C


class IndependentIntegration(unittest.TestCase):
    def test_learned_signed_energy_and_heldout_drift(self):
        spec=dict(profile=[['0','3','2/3'],['7/2','17/3','-5/4']],theta=['1/257','3/7','4/5'])
        discovery=S.make_data(spec,list(range(1,18)))
        adaptation=S.make_data(spec,[1]+list(range(8,34)))
        self.assertTrue(C.verify_data(discovery)['verified'])
        self.assertTrue(C.verify_data(adaptation)['verified'])
        result=S.discover(discovery,adaptation,'18/17',adaptive_rounds=2)
        merged=S.join_data(discovery,adaptation)
        for step in result['history']:
            certificate=step['candidate']
            verdict=C.verify_candidate(certificate,merged)
            self.assertTrue(verdict['verified'],verdict)
            self.assertFalse(verdict['uniform_recurrence_proved'])
        cert=result['candidate']
        final=S.make_data(spec,[1]+list(range(17,58)))
        self.assertTrue(C.verify_data(final)['verified'])
        children=list(range(34,58))
        independent=C.evaluate_candidate(cert,final,scales=children)
        actual=S.evaluate(cert,final,children)
        self.assertEqual(independent['status'],actual['status'])
        self.assertEqual(independent['violating_scales'],actual['violating_scales'])
        self.assertEqual(independent['inconclusive_scales'],actual['inconclusive_scales'])
        self.assertEqual(Q(independent['worst_lower']),actual['worst_lower'])
        self.assertEqual(Q(independent['worst_upper']),actual['worst_upper'])
        self.assertFalse(independent['RH_proved'])


if __name__=='__main__': unittest.main()
