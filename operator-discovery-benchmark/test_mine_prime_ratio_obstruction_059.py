"""Synthetic exact-cell and policy-scope checks; no059 source values."""
from fractions import Fraction as Q
import unittest

import mine_prime_ratio_obstruction_059 as M

METER=M.SEARCH.Meter()


class MinerTests(unittest.TestCase):
    def test_first_missing_prime_uses_actual_primes(self):
        self.assertEqual(M.first_missing_prime([2,5,7,11],METER),3)
        self.assertEqual(M.first_missing_prime([2,3,5,7,11,13,17,19],METER),23)

    def test_cells_keep_all_twelve_floors_constant(self):
        parameters={'p':2,'q':5,'primes':[2,5],'alpha':'2/7','gamma':'1','tau':'1/2'}
        result=M.floor_cells(parameters,32,METER)
        self.assertTrue(result['admissible_cells'])
        for cell in result['admissible_cells']:
            lo,hi=map(Q,(cell['cell']['lower'],cell['cell']['upper']))
            for base in (2,5,6,15):
                for factor in (1,2,4):
                    mid=(lo+hi)*factor/(2*base);floor=mid.numerator//mid.denominator
                    self.assertLessEqual(Q(floor),factor*lo/base)
                    self.assertLessEqual(factor*hi/base,Q(floor+1))
            self.assertGreater(Q(cell['cofactor_density_window']),0)
            self.assertIn(Q(cell['log_power']),(Q(19,7),Q(26,7)))

    def test_no_prior_or_reverse_prime_pass_is_admitted(self):
        scan=M.SEARCH._scan()
        forward={'kind':'prime_ratio','group':'profile','order':'asc'}
        reverse=dict(forward,order='desc')
        self.assertTrue(M.eligible({'steps':[forward,scan]}))
        self.assertTrue(M.eligible({'steps':[dict(forward,group='all')]}))
        self.assertFalse(M.eligible({'steps':[scan,forward]}))
        self.assertFalse(M.eligible({'steps':[reverse,scan]}))
        self.assertFalse(M.eligible({'steps':[]}))


if __name__=='__main__':unittest.main()
