import unittest
from fractions import Fraction as F
import complete_gram_storage_diagnostic as S

class Storage(unittest.TestCase):
    def fixture(self):
        parent=[['0']*14 for _ in range(14)];child=[['0']*14 for _ in range(14)]
        child[0][0]='1'
        return dict(gram_specs=S.B.gram_specs(),gram_duals=dict(full_parent={'matrix':parent},full_child={'matrix':child}))

    def test_increment_orientation_and_coercive_anchor(self):
        d=self.fixture();d['gram_duals']['full_parent']['matrix'][1][1]='1'
        out=S.compute(d)
        self.assertEqual(out['status'],'witness_invalid_for_anchored_storage_cone')
        self.assertEqual(out['quadratic_value'],'-4')
        self.assertEqual(out['state_matrix'][0][0],'1')
        self.assertEqual(out['state_matrix'][1][1],'1')
        self.assertEqual(out['increment_formal_constant_per_X'],'0')

    def test_constant_charge_and_nonnegative_extension(self):
        d=self.fixture();self.assertEqual(S.compute(d)['status'],'witness_extends_to_anchored_storage_cone')
        d['gram_duals']['full_parent']['matrix'][5][5]='1'
        self.assertEqual(S.compute(d)['increment_formal_constant_per_X'],'-1/2')

    def test_recovery_identity_polynomial_orientation(self):
        # Original lhs=budget-(child-prefix^2-4parent-prefix^2).
        # Subtracting the innovation column gives the anchored state target.
        p,c,hp,hc,D=map(F,[2,3,-1,4,20])
        original=D-(c*c-4*p*p);increment=hc*hc-4*hp*hp
        transformed=D-((c*c+hc*hc)-4*(p*p+hp*hp))
        self.assertEqual(original-increment,transformed)

if __name__=='__main__':unittest.main()
