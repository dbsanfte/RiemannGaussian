import copy
from fractions import Fraction as Q
import unittest

import mobius_prime_storage_073 as S


def direct_mu(n):
    sign, omega, largest = 1, 0, 1
    for p in range(2, n + 1):
        if n % p:
            continue
        count = 0
        while n % p == 0:
            n //= p
            count += 1
        if count:
            sign *= -1
            omega += 1
            largest = p
            if count > 1:
                sign = 0
    return sign, omega, largest


class PrimeStorageTests(unittest.TestCase):
    def test_generic_signed_source_with_unit_and_gaps(self):
        spec = dict(profile=[['0','7/3','-2/3'],['3','13/2','5/7']], theta=['1/257','2/5','7/8'])
        data = S.make_data(spec, [1,2,5,9])
        for row in data['rows']:
            expected = [Q(0)] * len(data['labels'])
            for n in range(1, row['X'] + 1):
                mu, omega, prime = direct_mu(n)
                w = sum((Q(v) for a,b,v in spec['profile'] if Q(a)*row['k'] < n <= Q(b)*row['k']), Q(0))
                value = mu*w
                expected[0] += value
                expected[1 if n == 1 else min(omega,4)+1] += value
                for j, cutoff in enumerate(row['cuts']):
                    if prime <= cutoff:
                        expected[6+j] += value
            self.assertEqual(expected,[Q(x,data['denominator']) for x in row['state']])

    def test_source_unit_and_all_prime_sectors_are_complete(self):
        data = S.make_data(dict(profile=[['0','12','1']], theta=['1/2']),[1,3])
        for row in data['rows']:
            self.assertEqual(row['state'][0],sum(row['state'][1:6]))
            self.assertEqual(row['state'][1],1)
            self.assertLess(row['state'][2],0)

    def test_normalizer_arbitrary_rational_and_exact_power(self):
        for k in (1,2,17,257):
            for q in (Q(1),Q(18,17),Q(258,257),Q(7,6),Q(2)):
                lo,hi=S.power_bounds(k,q,12)
                self.assertLessEqual(lo**q.denominator,k**q.numerator)
                self.assertGreaterEqual(hi**q.denominator,k**q.numerator)
                self.assertGreater(lo,0)
        self.assertEqual(S.power_bounds(64,Q(4,3)),(Q(256),Q(256)))

    def test_resource_gates_reject_large_power_before_allocation(self):
        with self.assertRaises(ValueError): S.power_bounds(100,Q(100002,100001))
        with self.assertRaises(ValueError): S.floor_power(100,Q(100001))
        with self.assertRaises(ValueError): S.make_data(S.SOURCE_SPEC,[1_000_000])

    def test_no_silent_profile_overlap_or_noncanonical_exponents(self):
        bad=copy.deepcopy(S.SOURCE_SPEC);bad['theta']=['2/4']
        with self.assertRaises(ValueError): S.make_data(bad,[1])
        bad=copy.deepcopy(S.SOURCE_SPEC);bad['profile'][1][0]='9'
        with self.assertRaises(ValueError): S.make_data(bad,[1])

    def test_square_keeps_signed_cross_terms(self):
        rays=[(Q(3,2),[1,-1],1)]
        self.assertEqual(S.energy([4,4],1,rays),16)
        self.assertEqual(S.energy([4,-4],1,rays),112)

    def test_generic_mode_elimination_and_exact_density_filter(self):
        rows=[[1,2,0,3],[2,4,0,6],[0,1,1,0]]
        basis=S.exact_nullspace(rows,4)
        self.assertEqual(len(basis),2)
        for v in basis:
            self.assertTrue(all(sum(a*b for a,b in zip(row,v))==0 for row in rows))
        scales=[1,2,4,8,16,32]+[64]*len(S.SOURCE_SPEC['theta'])
        basis=S.admissible_basis(S.SOURCE_SPEC,scales,Q(1))
        self.assertEqual(len(basis),len(scales)-3)
        for u in basis:
            v=[a/s for a,s in zip(u,scales)]
            self.assertEqual(v[2],v[5]);self.assertEqual(v[3],v[5]);self.assertEqual(v[4],v[5])
        zero_mass=dict(profile=[['0','1','1'],['1','2','-1']],theta=[])
        self.assertEqual(S.bulk_modes(zero_mass,Q(1))[0],[])
        self.assertEqual(S.bulk_modes(S.SOURCE_SPEC,Q(2))[0],[])

    def test_same_source_join_rejects_disagreement(self):
        data=S.make_data(S.SOURCE_SPEC,[1,2,3])
        broken=copy.deepcopy(data);broken['rows'][1]['state'][0]+=1
        with self.assertRaises(ValueError): S.join_data(data,broken)

    def test_exact_drift_distinguishes_refutation_and_missing_parent(self):
        data=dict(rows=[dict(k=1,state=[1]),dict(k=2,state=[4]),dict(k=3,state=[1])],denominator=1)
        cert=dict(rays=[],q='1',precision=20,C='6')
        result=S.evaluate(cert,data,[2,3])
        self.assertEqual(result['status'],'REFUTED')
        self.assertEqual(result['violating_scales'],[2])
        self.assertEqual(result['worst_lower'],7)
        with self.assertRaises(ValueError): S.evaluate(cert,data,[4])

    def test_discovery_exact_admission_never_claims_uniform_recurrence(self):
        # Synthetic source, not the scientific source/profile or its outcomes.
        spec=dict(profile=[['0','3','1'],['4','5','-2']],theta=['2/5','3/4'])
        discovery=S.make_data(spec,list(range(1,13)))
        adaptation=S.make_data(spec,[1]+list(range(6,25)))
        result=S.discover(discovery,adaptation,'18/17',adaptive_rounds=2)
        merged=S.join_data(discovery,adaptation)
        cert=result['candidate']
        verdict=S.evaluate(cert,merged,cert['training_scales'])
        self.assertEqual(verdict['status'],'VERIFIED_ON_FINITE_DOMAIN')
        self.assertEqual(Q(cert['C']),max(Q(0),verdict['worst_upper']))
        self.assertTrue(cert['uniform_domination_proved'])
        self.assertFalse(cert['uniform_recurrence_proved'])
        self.assertFalse(cert['RH_proved'])
        self.assertTrue(all(Q(r['weight'])>0 for r in cert['rays']))
        self.assertTrue(S.verify_bulk_centering(cert))


if __name__=='__main__': unittest.main()
