"""New uniform-capacity, arithmetic-exchange and robust-bound tests."""
from fractions import Fraction as Q
from math import gcd
from types import SimpleNamespace
from unittest.mock import patch
import unittest
import mobius_exchange_law_072 as S

METER=S.Meter(cap=300_000_000_000)


class ExchangeLawTests(unittest.TestCase):
    def test_multiplier_labels_and_masks(self):
        primes,entries=S.multiplier_dictionary(23,METER)
        self.assertEqual(primes,[2,3,5,7,11,13,17,19,23])
        for n,(sgn,mask) in entries.items():
            factors=[p for i,p in enumerate(primes) if mask&(1<<i)]
            product=1
            for p in factors:product*=p
            self.assertEqual(product,n);self.assertEqual(sgn,(-1)**len(factors))
        self.assertTrue(all(n not in entries for n in (4,8,9,12,16,18,20)))

    def test_general_profile_recovers_unnominated_semiprime_exchange(self):
        profile=[dict(lo='10/3',hi='5',value='2')]
        _,_,families=S.enumerate_families(profile,7,METER)
        self.assertTrue(any(f['a']==5 and f['b']==6 and Q(f['gain'])==4 for f in families))
        for f in families:self.assertGreater(Q(f['hi']),Q(f['lo']))

    def test_no_gain_and_known_pair_calibrations_separate_from_selection(self):
        c=S.construct(S.SOURCE_PROFILE,3,METER)
        self.assertEqual(c['candidates'],[]);self.assertEqual(c['leading_upper'],'6')
        _,_,families=S.enumerate_families(S.SOURCE_PROFILE,7,METER)
        pair=next(f for f in families if f['a']==3 and f['b']==5)
        self.assertEqual((pair['lo'],pair['hi']),('16/5','10/3'))
        self.assertTrue(any(f['a']==3 and f['b']==7 for f in families))

    def test_capacity_covers_exact_boundary_integer_incidence(self):
        primes,entries,families=S.enumerate_families(S.SOURCE_PROFILE,7,METER)
        patterns={tuple(row) for row in S.capacity_rows(primes,entries,families,METER)}
        for k in (1,2,3,5,7,11):
            for n in range(1,20*k+1):
                # Only squarefree indices are in the proof's capacity domain.
                if any(n%(d*d)==0 for d in range(2,int(n**.5)+1)):continue
                incidence=[]
                for i,f in enumerate(families):
                    a,b=f['a'],f['b']
                    for v in (a,b):
                        if n%v==0 and gcd(n//v,a*b)==1 and Q(f['lo'])*k<n//v<=Q(f['hi'])*k:
                            incidence.append(i)
                if incidence:self.assertIn(tuple(incidence),patterns)

    def test_exact_all_scale_cost_and_feasible_fractional_weights(self):
        c=S.construct([dict(lo='5/2',hi='17/3',value='-3/2'),dict(lo='8',hi='11',value='2/3')],7,METER)
        weights=[Q(v,c['lambda_denominator']) for v in c['lambda_numerators']]
        self.assertTrue(all(sum(weights[i] for i in row)<=1 for row in c['capacity_rows']))
        self.assertLessEqual(Q(c['objective_gain']),Q(c['objective_upper']))
        self.assertLessEqual(Q(c['leading_lower']),Q(c['leading_upper']))
        self.assertTrue(c['uniform_profile_bound_proved']);self.assertFalse(c['uniform_head_bound_proved'])

    def test_dual_defect_remains_paid_with_zero_dual(self):
        p,e,f=S.enumerate_families(S.SOURCE_PROFILE,7,METER);rows=S.capacity_rows(p,e,f,METER)
        result=S.prices(S.SOURCE_PROFILE,e,f,rows,[0]*len(f),S.GRID,[0]*len(rows),METER)
        expected=sum((Q(c['gain'])*Q(c['density_ratio'])*(Q(c['hi'])-Q(c['lo'])) for c in f),Q(0))
        self.assertEqual(Q(result['objective_upper']),expected);self.assertEqual(result['objective_gain'],'0')
        self.assertGreater(expected,0)

    def test_root_enclosures_include_zero_and_fractional_endpoints(self):
        for x in (Q(0),Q(1),Q(3,7),Q(16,5),Q(1,257),Q(121,16)):
            u=S.root_upper(x);self.assertGreaterEqual(u*u,x)
            if u:self.assertLess((u-Q(1,S.GRID))**2,x)

    def test_solver_failure_retains_sound_zero_allocation(self):
        failed=SimpleNamespace(success=False,nit=2,message='synthetic incomplete optimization')
        with patch.object(S,'linprog',return_value=failed):c=S.construct(S.SOURCE_PROFILE,7,METER)
        self.assertEqual(c['selected_family_indices'],[])
        self.assertEqual(c['leading_upper'],'6');self.assertEqual(c['solver']['status'],'failed_zero_fallback')

    def test_invalid_profiles_and_resource_limits_reject(self):
        for profile in ([dict(lo='1',hi='1',value='1')],[dict(lo='0',hi='2',value='0')],
                        [dict(lo='0',hi='2',value='1'),dict(lo='1',hi='3',value='1')]):
            with self.assertRaises(ValueError):S.construct(profile,3,METER)
        with self.assertRaises(ValueError):S.construct(S.SOURCE_PROFILE,24,METER)
        with self.assertRaises(OverflowError):S.construct(S.SOURCE_PROFILE,7,S.Meter(cap=1))


if __name__=='__main__':unittest.main()
