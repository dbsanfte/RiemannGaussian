"""Exact calibration, grammar coverage and proof-scope tests; no full search."""
from collections import Counter
from copy import deepcopy
from fractions import Fraction as Q
from math import comb
import unittest
import prime_slide_discovery as P
import run_prime_slide_discovery as R

METERS=[]
def meter():
    m=P.Meter();METERS.append(m);return m
def tearDownModule():
    print('SYNTHETIC_WORK module=test_prime_slide_discovery operations='+str(sum(m.operations for m in METERS)))


class SlideTests(unittest.TestCase):
    def test_generating_series_rows_on_unrelated_exact_parameters(self):
        m=meter();engine=P.Engine(m)
        def evaluate(row,t):
            m.charge(2*len(row));return sum((c*t**e[0] for e,c in row.items()),Q(0))
        for t in (Q(2,7),Q(3,5)):
            au=[Q(1)]+[t**e-t**(e-1) for e in range(1,7)]
            av=[Q(1)]+[t**(2*e)-t**(2*e-2) for e in range(1,7)]
            for e in range(7):
                m.charge(2*e+8)
                self.assertEqual(evaluate(engine.locals[0][e],t),sum(au[j]*av[e-j] for j in range(e+1)))
                self.assertEqual(evaluate(engine.locals[1][e],t),au[e])
                self.assertEqual(evaluate(engine.locals[2][e],t),av[e])

    def test_declared_grammar_coverage_without_scoring_candidates(self):
        m=meter();counts=Counter();catalogue=[]
        for identity,(family,program) in enumerate(P.programmes()):
            P.validate(program);counts[family]+=1;m.charge(12+len(program['terms'])*8)
            # Only grammar membership/coverage is tested here; these placeholders
            # are not candidate algebra or search scores.
            catalogue.append(dict(id=identity,family=family,program=program,
                exact_zero_all_components=True,component_valuations=[None]*9))
        primitive=lambda k:(4**k-2**k)//2
        self.assertEqual(counts['same_prime_sparse'],sum(comb(15,k)*primitive(k) for k in (1,2,3)))
        self.assertEqual(counts['same_prime_rectangles'],comb(10,4))
        self.assertEqual(counts['distinct_prime_sparse'],sum(comb(4,k)*primitive(k) for k in range(1,5)))
        self.assertEqual(set(counts),{'same_prime_sparse','same_prime_rectangles','distinct_prime_sparse'})
        R.audit_catalogue(catalogue,[],m)
        catalogue[0]['program']['terms'][0]['coefficient']=2
        with self.assertRaisesRegex(ValueError,'normalization'):R.audit_catalogue(catalogue,[],m)

    def test_repeated_prime_is_not_two_distinct_prime_actions(self):
        m=meter();engine=P.Engine(m)
        same=P.make_same([(2,0),(1,1),(0,2)],[1,-2,1]);s=engine.facts(same)
        distinct=dict(binding='distinct_primes',terms=[
            dict(coefficient=c,left=l,right=r) for c,l,r in (
                (1,[1,1],[0,0]),(-1,[1,0],[0,1]),(-1,[0,1],[1,0]),(1,[0,0],[1,1]))])
        d=engine.facts(distinct)
        self.assertEqual(s['component_valuations'][5],[0]);self.assertEqual(d['component_valuations'][5],[1,1])
        self.assertEqual(d['common_valuations'],[0,0])  # common B sectors remain
        self.assertEqual(s['multipliers'][5][0],[[0],-2])
        self.assertFalse(d['whole_signed_bound_proved'])

    def test_cumulative_operator_has_a_bound_but_recovery_stays_open(self):
        m=meter();engine=P.Engine(m)
        program=P.make_same([(e,0) for e in range(6)],[1]*6)
        row=P.record(0,'calibration_only',program,engine)
        self.assertEqual(row['common_valuations'],[4]);self.assertEqual(row['bound']['energy_power'],'0')
        self.assertTrue(row['auxiliary_cofinal_bound_proved']);self.assertFalse(row['original_target_recovered'])
        self.assertFalse(row['whole_signed_bound_proved']);self.assertEqual(len(row['recovery_obligations']),5)
        self.assertEqual(row['baseline_coefficient'],1)
        f=engine.facts(program)
        self.assertEqual(f['multipliers'][0],[[[4],-1],[[9],1],[[10],1]])
        self.assertEqual(f['multipliers'][3],[[[5],1]])
        self.assertEqual(f['multipliers'][6],[[[10],1]])

    def test_free_index_count_and_positive_power_remainders(self):
        m=meter()
        b=P.support_bound('distinct_primes',['1/3','1/3'],'3/4',m)
        self.assertEqual(b['energy_power'],'1/2');self.assertFalse(b['cofinal_auxiliary'])
        self.assertEqual(b['prime_count'],2)
        b=P.support_bound('same_prime',['4/3'],'3/4',m)
        self.assertEqual(b['energy_power'],'0');self.assertTrue(b['cofinal_auxiliary'])
        b=P.support_bound('same_prime',['5/3'],'3/4',m)
        self.assertEqual(b['energy_power'],'-1/4')
        for args in (('same_prime',['1/3','1/3'],'3/4'),('distinct_primes',['2/3'],'3/4'),('same_prime',['0'],'3/4')):
            with self.assertRaises(ValueError):P.support_bound(*args,m)

    def test_validation_rejects_invalid_prime_binding_and_hidden_actions(self):
        good=P.make_same([(1,0)],[1]);P.validate(good)
        for bad in (dict(good,binding='unknown'),dict(good,id=0),P.make_same([(1,0)],[True]),
                    P.make_same([(7,0)],[1]),P.make_same([(4,3)],[1]),P.make_same([(1,0),(1,0)],[1,-1])):
            with self.assertRaises(ValueError):P.validate(bad)
        m=P.Meter(cap=2);METERS.append(m)
        with self.assertRaises(OverflowError):m.charge(3)
        self.assertEqual(m.operations,0)
        m=meter()
        with self.assertRaises(MemoryError):m.live(12000001)

    def test_certificate_audit_rejects_recovery_geometry_and_scope_corruption(self):
        m=meter();engine=P.Engine(m)
        row=P.record(0,'calibration_only',P.make_same([(e,0) for e in range(6)],[1]*6),engine)
        R.audit_record(row,m)
        bad=deepcopy(row);bad['recovery_obligations'].pop()
        with self.assertRaisesRegex(ValueError,'recovery'):R.audit_record(bad,m)
        bad=deepcopy(row);bad['bound']['index_support']='h<=n/q,k<=n/q'
        with self.assertRaisesRegex(ValueError,'geometry'):R.audit_record(bad,m)
        bad=deepcopy(row);bad['bound']['original_target_recovered']=True
        with self.assertRaisesRegex(ValueError,'scope'):R.audit_record(bad,m)
        bad=deepcopy(row);bad['tensor_coefficients'][0]=0
        with self.assertRaisesRegex(ValueError,'tensor'):R.audit_record(bad,m)
        bad=deepcopy(row);bad['multipliers'][0][0][1]=0
        with self.assertRaisesRegex(ArithmeticError,'polynomial'):R.audit_record(bad,m)

    def test_selection_retains_recovery_lane_and_whole_tensor_priority(self):
        # Ranking fixtures, not new arithmetic candidate measurements.
        m=meter()
        def row(identity,baseline,cofinal,power,mixed):
            return dict(id=identity,family='same_prime_sparse',baseline_coefficient=baseline,
                exact_zero_all_components=False,program=dict(binding='same_prime'),
                bound=dict(cofinal_auxiliary=cofinal,energy_power=power) if power is not None else None,
                auxiliary_cofinal_bound_proved=cofinal,term_count=3,coefficient_l1=4,
                component_valuations=[[0]]*5+[[mixed]]+[[0]]*3)
        records=[row(0,1,False,None,9),row(1,1,True,'0',4),row(2,0,True,'-1/4',5)]
        m.charge(60)
        self.assertEqual(P.selected(records),[1,2,0])
        self.assertEqual(P.selected(list(reversed(records))),[1,2,0])


if __name__=='__main__':unittest.main()
