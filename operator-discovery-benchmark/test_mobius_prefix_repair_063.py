"""Synthetic tests for exact analytic repair constructors."""
from fractions import Fraction as Q
from math import gcd
import unittest

import mobius_prefix_repair_063 as S
import mobius_prefix_completion_062 as B
import check_mobius_prefix_completion_062 as C

METER=S.Meter()
PARAMS={'alpha':'1/257','gamma':'1/3','tau':'3/4','primes':[2,7],'p':2,'q':7}


def base():
    raw=B.inverse_completion(31,23,6,PARAMS,METER)
    return B.exact_certificate(31,23,6,PARAMS,raw['endpoints'],METER)


class RepairSearchTests(unittest.TestCase):
    def test_inverse_arbitrary_signed_fractional_sequence(self):
        values=list(map(Q,['7/11','-2','1/257','4','0','9/5','-1']))
        cs=S.inverse_floor(values,S.ordinary_mu(len(values),METER),METER)
        for d in range(1,len(values)+1):
            self.assertEqual(sum((c*(j//d) for j,c in enumerate(cs,1)),Q(0)),values[d-1])
            METER.charge(20*len(values))

    def test_large_floor_residual_has_unit_repair(self):
        values=[Q(19//d) for d in range(1,20)]
        cs=S.inverse_floor(values,S.ordinary_mu(19,METER),METER)
        self.assertEqual(cs,[Q(0)]*18+[Q(1)])
        self.assertGreater(sum(values),sum(map(abs,cs)))

    def test_fill_rules_preserve_every_coprime_row_and_boundary(self):
        values=list(map(Q,range(1,11)))
        for rule in S.RULES:
            filled=S.fill_rows(values,[2,7],rule,METER)
            for d in range(1,11):
                if gcd(d,14)==1:self.assertEqual(filled[d-1],values[d-1])
        self.assertEqual(S.fill_rows(values,[2,7],'right',METER)[9],0)
        self.assertEqual(S.fill_rows(values,[2,7],'core_inverse',METER)[7],Q(1,8))

    def test_reciprocal_fill_recovers_inverse_distance(self):
        values=[Q(1,d) for d in range(1,14)]
        filled=S.fill_rows(values,[2,7],'reciprocal_linear',METER)
        for d in range(1,13):self.assertEqual(filled[d-1],Q(1,d))

    def test_all_recipes_create_exact_whole_source_completion(self):
        old=base();result=S.discover(old,METER)
        for candidate in result['candidates']:
            cm=C.Meter();v=C.verify_completion(candidate['completion'],cm);METER.charge(cm.operations)
            self.assertTrue(v['finite_prefix_bound_proved'])
            self.assertTrue(all(Q(e['short_residual_l1'])==0 for e in v['endpoint_costs']))
            self.assertFalse(v['uniform_N_growth_proved'])
        self.assertEqual(Q(result['selected_budget']),min(Q(c['new_budget']) for c in result['candidates']))

    def test_unit_and_moment_retained_by_repair(self):
        old=base();result=S.discover(old,METER)
        for candidate in result['candidates']:
            repair=candidate['repair']
            for residual,cs in zip(repair['residuals'],repair['coefficients']):
                self.assertEqual(sum((j*Q(c) for j,c in enumerate(cs,1)),Q(0)),Q(residual[0]))

    def test_generic_long_equals_full_inverse_above_H(self):
        N,y,H=31,23,6;old=base();p,q=2,7
        for endpoint,ratio in enumerate((Q(p,q),Q(1))):
            values=[Q(B.weight(N,p,d))-ratio*B.weight(N,q,d) if d<=y else Q(0) for d in range(1,4*N//p+1)]
            cs=S.inverse_floor(values,S.ordinary_mu(len(values),METER),METER)
            expected={j:c for j,c in enumerate(cs,1) if j>H and c}
            actual={X:Q(c) for X,c in zip(old['horizons'],old['coefficients'][endpoint]) if Q(c)}
            self.assertEqual(expected,actual)

    def test_invalid_rule_and_wrong_long_support_rejected(self):
        with self.assertRaises(ValueError):S.fill_rows([Q(1)],[2,7],'invented',METER)
        old=base();old['horizons'].append(1)
        for row in old['coefficients']:row.append('0')
        with self.assertRaisesRegex(ValueError,'long horizons'):S.short_residuals(old,METER)


class QuadraticLiftTests(unittest.TestCase):
    def test_factored_form_matches_direct_bilinear_expansion(self):
        old=base()
        for rule in S.RULES:
            candidate=S.construct(old,rule,meter=METER)
            lift=S.quadratic_lift(old,rule,candidate['repair'],METER)
            u=lift['ordinary_mu_through_radius'];H,K=lift['H'],lift['K']
            for endpoint in range(2):
                f=list(map(Q,lift['linear_terms'][endpoint]))
                G=[list(map(Q,row)) for row in lift['long_kernels_after_fill'][endpoint]]
                for j in range(1,H+1):
                    value=Q(0)
                    for at,sign in ((j,1),(j+1,-1)):
                        for m in range(1,H//at+1):
                            value+=sign*u[m-1]*f[at*m-1]
                            for ell in range(1,K+1):
                                value-=sign*u[m-1]*u[ell-1]*G[at*m-1][ell-1]
                                METER.charge(30)
                    self.assertEqual(value,Q(candidate['repair']['coefficients'][endpoint][j-1]))
            self.assertEqual(lift['arithmetic_radius'],max(H,K))
            self.assertFalse(lift['uniform_quadratic_variation_bound_proved'])

    def test_fill_operators_are_linear(self):
        a=[Q(d,3) for d in range(1,12)];b=[Q((-1)**d,d) for d in range(1,12)]
        for rule in S.RULES:
            lhs=S.fill_rows([3*x-2*y for x,y in zip(a,b)],[2,7],rule,METER)
            pa=S.fill_rows(a,[2,7],rule,METER);pb=S.fill_rows(b,[2,7],rule,METER)
            self.assertEqual(lhs,[3*x-2*y for x,y in zip(pa,pb)])

    def test_quadratic_replay_rejects_modified_repair(self):
        old=base();candidate=S.construct(old,'raw',meter=METER)
        candidate['repair']['coefficients'][0][0]='12345'
        with self.assertRaisesRegex(ValueError,'every repair coefficient'):
            S.quadratic_lift(old,'raw',candidate['repair'],METER)


if __name__=='__main__':unittest.main()
