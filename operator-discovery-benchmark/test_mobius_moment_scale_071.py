"""New proof-language and small unrelated-source tests; no old study replay."""
from fractions import Fraction as Q
from types import SimpleNamespace
from unittest.mock import patch
import unittest
import mobius_moment_scale_071 as S

METER=S.Meter(cap=300_000_000_000)
PARAMS=dict(primes=[2,3,5],p=3,q=5,alpha='1/5',gamma='5/28',tau='1/2')


class MomentScaleTests(unittest.TestCase):
    def test_generic_optimum_on_unrelated_affine_problem(self):
        system=dict(variables=['a','b'],rows=[S.row('price',[2,1],5),S.row('gap',[1,-1],1),
                    S.row('a_nonnegative',[1,0],0),S.row('b_nonnegative',[0,1],0)],objective=['2','1'])
        cert=S.solve_system(system,METER)
        self.assertEqual(cert['status'],'optimal'); self.assertEqual(cert['objective'],'5')
        x,y=map(lambda v:list(map(Q,v)),(cert['primal'],cert['dual']))
        self.assertTrue(S.optimal_replay([list(map(Q,r['a'])) for r in system['rows']],
                        [Q(r['b']) for r in system['rows']],[Q(2),Q(1)],x,y))

    def test_generic_exact_farkas_and_unbounded_unknown(self):
        system=dict(variables=['x'],rows=[S.row('lower',[1],2),S.row('upper',[-1],-1)],objective=['1'])
        cert=S.solve_system(system,METER)
        self.assertEqual(cert['status'],'infeasible')
        self.assertTrue(S.farkas_replay([[Q(1)],[Q(-1)]],[Q(2),Q(-1)],list(map(Q,cert['dual']))))
        unbounded=dict(variables=['x'],rows=[S.row('upper',[-1],0)],objective=['1'])
        self.assertEqual(S.solve_system(unbounded,METER)['status'],'unresolved')

    def test_free_frontier_recovered_from_facets(self):
        # Independently reviewed calibration law, not a supplied search target.
        for s,r in [('1/2','1/2'),('1/2','2/3'),('1/2','3/4'),('3/7','4/5'),('5/9','7/8')]:
            cert=S.construct_program(s,r,meter=METER); d=cert['derivation']
            self.assertIsNotNone(d)
            self.assertEqual(Q(d['alpha']),max(Q(s),2-2*Q(r)))
            self.assertEqual(Q(d['exposure']),min(Q(r),1-Q(s)/2))
            self.assertFalse(cert['conditional_prefix_bounds_paid']); self.assertFalse(cert['RH_proved'])

    def test_unequal_cuts_and_impossible_exposure(self):
        feasible=S.construct_program('1/2','7/8','2/7',METER)
        self.assertEqual(feasible['derivation']['theta'],'2/7')
        for s,r,t in [('1/2','3/7',None),('3/5','4/5','1/9')]:
            bad=S.construct_program(s,r,t,METER)
            self.assertEqual(bad['primary']['result']['status'],'infeasible')
            self.assertIsNone(bad['secondary']); self.assertIsNone(bad['derivation'])

    def test_fractional_proof_search_not_root_whitelist(self):
        for s,r,t in [('1/257','256/257','1/257'),('11/23','19/23','7/19'),('37/1048583','7/8',None)]:
            cert=S.construct_program(s,r,t,METER)
            self.assertEqual(cert['primary']['result']['status'],'optimal')
            d=cert['derivation']; self.assertIsNotNone(d)
            self.assertEqual(Q(d['short_exponent']),1/(2-Q(s)))

    def test_short_rule_synthesizes_balance_and_keeps_constant(self):
        for s in ('1/11','4/7','6/7'):
            d=S.construct_program(s,'7/8',meter=METER)['derivation']
            delta=Q(d['short_exponent']); split=Q(d['short_split'])
            self.assertEqual(delta,Q(s)+(1-Q(s))*split)
            self.assertEqual(delta,1-split)
            self.assertEqual(Q(d['short_C_exponent']),delta)
            self.assertEqual(Q(d['short_per_branch_constant']),1+4/(1-Q(s)))

    def test_exact_root_ceiling_and_uniform_base(self):
        for R,e in [(1,'1/257'),(17,'1/257'),(256,'3/4'),(257,'3/4'),(343,'2/3')]:
            a=Q(e); lo=S.power(R,e,METER); hi=S.ceil_power(R,e,METER)
            self.assertLessEqual(lo**a.denominator,R**a.numerator)
            self.assertGreater((lo+1)**a.denominator,R**a.numerator)
            self.assertGreaterEqual(hi**a.denominator,R**a.numerator)
            self.assertLess((hi-1)**a.denominator,R**a.numerator)
        self.assertFalse(S.base_gate(15,'3/4',METER)); self.assertTrue(S.base_gate(16,'3/4',METER))
        self.assertFalse(S.base_gate(1,'1/2',METER))

    def test_full_C_polynomial_and_large_symbolic_base(self):
        cert=S.construct_program('1/257','256/257','1/257',METER); d=cert['derivation']
        a,A=Q(d['alpha']),Q(d['reciprocal_A'])
        for C in (1,3,19):
            self.assertEqual(sum(Q(v)*C**i for i,v in enumerate(d['head_C_polynomial'])),8/a*(1+A*C)**2)
        self.assertEqual(d['sufficient_base_log2'],257)

    def test_geometry_joins_source_and_retains_rank_bases(self):
        programs=[S.construct_program('2/5','3/4',meter=METER),S.construct_program('2/5','2/5',meter=METER)]
        cert=S.construct_source(23,5,30,PARAMS,programs,METER)
        for ep in cert['endpoints']:
            den=ep['denominator']; ratio=Q(ep['ratio'])
            def g(n):
                if n<=5 or n>30:return 0
                def W(p):return 92//(p*n)-3*(46//(p*n))+2*(23//(p*n))
                return -den*W(3)+ratio.numerator*W(5)
            for r in ep['rows']:
                self.assertEqual([p['program_index'] for p in r['plans']],[0])
                for n in range(1,r['R']+1):
                    self.assertEqual(sum(h for A,h in r['prefix_steps'] if n<=A),g(r['j']*n)-g((r['j']+1)*n))
            unit=ep['rows'][-1]['plans'][0]
            self.assertFalse(unit['strict_rank']); self.assertFalse(unit['universal_base_gate'])

    def test_failed_proposals_are_open_and_work_caps_are_not_swallowed(self):
        failed=SimpleNamespace(status=1,nit=2,message='synthetic time limit',success=False)
        with patch.object(S,'linprog',return_value=failed):
            cert=S.construct_program('1/2','3/4',meter=METER)
        self.assertEqual(cert['primary']['result']['status'],'unresolved'); self.assertIsNone(cert['derivation'])
        with self.assertRaises(OverflowError):
            S.construct_program('1/2','3/4',meter=S.Meter(cap=1))

    def test_false_optimum_and_separating_vectors_fail_exact_replay(self):
        A=[[Q(1)],[Q(-1)]]; b=[Q(0),Q(-1)]; c=[Q(1)]
        self.assertFalse(S.optimal_replay(A,b,c,[Q(1)],[Q(0),Q(0)]))
        self.assertFalse(S.farkas_replay(A,b,[Q(1),Q(1)]))
        with self.assertRaises(ValueError): S.construct_program('2/4','3/4',meter=METER)
        with self.assertRaises(ValueError): S.construct_program('1','3/4',meter=METER)


if __name__=='__main__':unittest.main()
