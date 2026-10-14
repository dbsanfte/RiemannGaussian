"""New integration: generated uniform laws on an unrelated rational profile."""
from fractions import Fraction as Q
import unittest
import mobius_exchange_law_072 as S
import check_mobius_exchange_law_072 as C

PM=S.Meter(cap=300_000_000_000)
CM=C.Meter()


class ExchangeIntegrationTests(unittest.TestCase):
    def test_generic_generated_law_and_integer_boundary_evaluation(self):
        profile=[dict(lo='0',hi='5/3',value='-2'),dict(lo='7/3',hi='19/3',value='3/2')]
        c=S.construct(profile,7,PM);v=C.verify_law(c,CM)
        self.assertTrue(v['verified']);self.assertTrue(v['uniform_profile_bound_proved'])
        for k in (1,3,7,13):
            e=C.evaluate_law(c,k,CM)
            self.assertTrue(e['verified'])
            self.assertLessEqual(Q(e['actual_absolute_target']),Q(e['certified_finite_price']))
            self.assertFalse(e['uniform_head_bound_proved']);self.assertFalse(e['RH_proved'])


if __name__=='__main__':unittest.main()
