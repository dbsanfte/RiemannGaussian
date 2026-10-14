import copy
from fractions import Fraction as Q
import unittest

import mobius_centered_storage_074 as S
import check_mobius_prime_storage_073 as C


class GrammarSearchTests(unittest.TestCase):
    def test_catalog_obeys_physical_rules_despite_unequal_scaling(self):
        spec=dict(profile=copy.deepcopy(S.PROFILE), theta=['17/53','1/2','17/31','53/64'])
        scale=[8,1,8,16,16,4,2,4,8,16]
        high=S.catalog(spec,scale,'65/64','centered_high')
        mixed=S.catalog(spec,scale,'65/64','open_mixed')
        self.assertTrue(high)
        self.assertTrue(set(high).issubset(set(mixed)))
        for u in high:
            v=[a/s for a,s in zip(u,scale)]
            self.assertEqual(v[6],0)
            self.assertEqual(sum(v[6:]),0)
            self.assertEqual(v[1:6],[0]*5)
        self.assertTrue(any(u[6] and sum(a/s for a,s in zip(u[6:],scale[6:])) for u in mixed))

    def test_boundary_bulk_and_unknown_mixture_are_distinct(self):
        spec=dict(profile=copy.deepcopy(S.PROFILE),theta=['2/7','1/2','4/5'])
        pure=['0']*7+['1','0']
        self.assertFalse(S.allowed(pure,spec,'1','open_mixed'))
        mixed=['0']*6+['1','0','1']
        self.assertTrue(S.allowed(mixed,spec,'1','open_mixed'))
        self.assertFalse(S.allowed(mixed,spec,'1','centered_high'))
        with self.assertRaises(ValueError):S.catalog(spec,[1]*9,'2','open_mixed')

    def test_small_discovery_has_independently_valid_exact_candidates(self):
        spec=dict(profile=copy.deepcopy(S.PROFILE),theta=['2/7','1/2','17/31','4/5'])
        data=S.B.make_data(spec,list(range(1,97)))
        discovery=dict(data,rows=data['rows'][:32])
        adaptation=dict(data,rows=data['rows'])
        for branch in S.BRANCHES:
            result=S.discover(discovery,adaptation,'9/8',branch,adaptive_rounds=2)
            cert=result['candidate']
            verdict=C.verify_candidate(cert,data)
            self.assertTrue(verdict.get('verified'),verdict)
            self.assertFalse(cert['uniform_recurrence_proved'])
            self.assertFalse(cert['RH_proved'])
            for ray in cert['rays']:
                self.assertTrue(S.allowed(ray['direction'],spec,'9/8',branch))


if __name__=='__main__':unittest.main()
