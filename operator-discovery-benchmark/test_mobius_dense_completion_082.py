import copy
import unittest
from fractions import Fraction as Q
import numpy as np

import mobius_dense_completion_082 as S
import check_mobius_dense_completion_082 as C


def program(extended=False, memory=2):
    kernel = [(4, '-1'), (5, '1'), (8, '1'), (10, '-1')]
    if extended:
        kernel += [(12, '-3547/8192'), (15, '3547/8192'), (24, '3547/8192'), (30, '-3547/8192')]
    profiles = [{'scale':'1/4', 'eta':'1'}, {'scale':'3/2', 'eta':'3/7'}]
    return dict(schema='dense-divisor-completion-v1',
                kernel=[dict(divisor=d, weight=w) for d, w in sorted(kernel)],
                memory=memory, rays=[dict(a=['1']*memory, weight='1/4')],
                drift_multiplier='3/2', profiles=profiles,
                theta=[['0']*(memory+1) for _ in profiles],
                gram_weights=['0']*(memory+1+len(profiles)))


def mobius(n):
    # Test-only literal trial factors, never supplied to search/selection.
    sign = 1; p = 2
    while p*p <= n:
        if n % p == 0:
            n //= p; sign = -sign
            if n % p == 0:
                return 0
        p += 1
    return -sign if n > 1 else sign


class DenseSearchTests(unittest.TestCase):
    def test_exact_arbitrary_rational_roots(self):
        for s, e in [('3/2','3/7'), ('2/9','8/11'), ('7/3','5/13'), ('1/4','1')]:
            u = 1777; x = S.floor_scaled_power(u, s, e); a, b = Q(s), Q(e)
            target = a.numerator**b.denominator*u**b.numerator
            den = a.denominator**b.denominator
            self.assertLessEqual(x**b.denominator*den, target)
            self.assertGreater((x+1)**b.denominator*den, target)
        with self.assertRaises(S.ResourceLimit):
            S.floor_scaled_power(10, '2', '1/100001')

    def test_literal_groups_match_independent_breakpoints(self):
        for u in (1, 7, 137, 401):
            p = program(extended=True, memory=3)
            left, right = S.build_model(p, u), C.build_model(p, u)
            features = tuple(tuple(Q(int(v), left['denominator']) for v in row) for row in left['features'])
            self.assertEqual(features, right['features'])
            self.assertEqual(tuple(map(int, left['counts'])), right['counts'])
            self.assertEqual(left['T'], right['T'])
            self.assertEqual(left['cuts'], list(right['cuts']))

    def test_all_squarefree_coordinates_unit_and_prime_band(self):
        p = program(); model = S.build_model(p, 401)
        self.assertEqual(model['squarefree_count'], sum(mobius(n)**2 for n in range(1, 101)))
        self.assertEqual(int(sum(model['counts'])), model['squarefree_count'])
        self.assertEqual(model['cuts'][0], 100)
        self.assertTrue(any(row[-2] == 99 for row in model['features']))

    def test_zero_identity_and_complete_dense_actual_bound(self):
        p = program(extended=True)
        p['theta'] = [['1/8','-1/7','2/9'], ['-3/11','1/13','0']]
        p['gram_weights'] = ['0','1/7','0','1/13','2/17']
        u = 211; model = S.build_model(p, u); parsed = model['program']; d = p['memory']+1
        nmax = model['N']; mu = {n:mobius(n) for n in range(1,nmax+1)}
        for K in model['cuts']:
            self.assertEqual(sum(mu[n]*(K//n-int(n==1)) for n in mu), 0)
        source = [sum(Q(w)*sum(mu[n] for n in range(1,min(nmax,u//(dv*2**i))+1))
                      for dv,w in parsed['kernel']) for i in range(d)]
        drift = sum(model['T'][i][j]*source[i]*source[j] for i in range(d) for j in range(d))
        cert = S.upper_certificate(model)
        checked = C.verify_certificate(p,u,cert)
        self.assertEqual(checked['status'],'VERIFIED_FINITE_DENSE_UPPER_BOUND')
        self.assertGreaterEqual(Q(cert['price']),drift)
        self.assertFalse(checked['uniform_growth_proved'])

    def test_empty_horizon_exact_certificate(self):
        p=program(); cert=S.upper_certificate(S.build_model(p,1))
        self.assertEqual(cert,dict(group_count=0,squarefree_count=0,price='0',row_prices=[]))
        self.assertEqual(C.verify_certificate(p,1,cert)['status'],'VERIFIED_FINITE_DENSE_UPPER_BOUND')

    def test_exact_dual_valid_and_tampering_rejected(self):
        p=program(); model=S.build_model(p,91); n=model['group_count']
        lambdas=[Q(1,2)]*n; nus=[Q(-1,3)]*(n*(n-1)//2)
        cert=S.dual_certificate(model,lambdas,nus)
        checked=C.verify_price_dual(p,91,cert)
        self.assertEqual(checked['status'],'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND')
        self.assertLessEqual(Q(cert['lower_bound']),Q(S.upper_certificate(model)['price']))
        bad=copy.deepcopy(cert);bad['lower_bound']=str(Q(cert['lower_bound'])+1)
        self.assertEqual(C.verify_price_dual(p,91,bad)['status'],'INVALID')

    def test_lp_proposal_exactly_admitted_both_sides(self):
        p=program(); row=S.optimize(p,131,time_limit=30)
        self.assertEqual(row['status'],'LP_PROPOSAL')
        self.assertEqual(C.verify_certificate(row['program'],131,row['certificate'])['status'],'VERIFIED_FINITE_DENSE_UPPER_BOUND')
        self.assertEqual(C.verify_price_dual(row['program'],131,row['dual'])['status'],'VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND')
        self.assertGreaterEqual(Q(row['exact_gap']),0)
        self.assertFalse(row['signs_or_source_values_used'])

    def test_full_coordinate_resource_rejection(self):
        with self.assertRaises(S.ResourceLimit):
            S.build_model(program(), 4*(S.MAX_N+1))
        p=program(); p['kernel'][0]['weight']=str(Q(-1,2**90+1))
        with self.assertRaises(S.ResourceLimit):
            S.build_model(p,100)

    def test_sublinear_uniform_obstruction_source_binding(self):
        p=program();p['profiles'][0]={'scale':'9/5','eta':'7/11'}
        cert=S.sublinear_obstruction(p)
        self.assertEqual(cert['status'],'PROVED_SUBLINEAR_PROFILE_PRICE_OBSTRUCTION')
        u=cert['threshold']
        self.assertGreaterEqual(u,58081)
        for profile in p['profiles']:
            self.assertLessEqual(S.floor_scaled_power(u,profile['scale'],profile['eta']),u//5)
        self.assertEqual(cert['quadratic_coefficient'],'1/5120')
        self.assertEqual(S.sublinear_obstruction(program())['status'],'NOT_APPLICABLE')
        p['kernel'][0]['weight']='-2'
        self.assertEqual(S.sublinear_obstruction(p)['status'],'NOT_APPLICABLE')

    def test_early_rational_growth_and_dual_admission(self):
        p=program()
        p['rays']=[dict(a=['1','1'],weight=str(Q(1,2**4080-v))) for v in range(1,35,2)]
        with self.assertRaises(S.ResourceLimit):
            S.build_model(p,131)
        m=S.build_model(program(),91);n=m['group_count']
        with self.assertRaises(S.ResourceLimit):
            S.dual_certificate(m,[Q(1,2**5000)]*n,[Q(0)]*(n*(n-1)//2))
        with self.assertRaises(ValueError):
            S.dual_certificate(m,['01']*n,['0']*(n*(n-1)//2))


if __name__=='__main__':
    unittest.main()
