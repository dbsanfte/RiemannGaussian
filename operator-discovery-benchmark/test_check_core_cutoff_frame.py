"""Hand-derived rational frames and synthetic integer source calibration only."""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import combinations
import json
import resource
import sys
import time
import unittest
from flint import arb,ctx

import check_core_cutoff_frame as CHECK
from potential_candidate_language import Meter

START=time.monotonic()
WORK=Meter(50000000,deadline=START+180,max_cells=1000000)


def catalogue(dimension=3):
    # Generic known nullspace vectors are a test fixture, never source choices.
    pairs=list(combinations(range(dimension),2));basis=[]
    for ident,(i,j) in enumerate(pairs):
        vector=[['0']*(dimension+1) for _ in range(dimension)]
        vector[i][j+1]='1';vector[j][i+1]='-1'
        sums=[str(sum(int(row[k]) for row in vector)) for k in range(dimension+1)]
        basis.append(dict(id=ident,vector=vector,sum=sums))
    candidates=[]
    def add(poly,monomial,coefficient):
        monomial=tuple(sorted(monomial));poly[monomial]=poly.get(monomial,0)+coefficient
        if not poly[monomial]:del poly[monomial]
    def encoded(poly):return [dict(monomial=list(m),coefficient=str(c)) for m,c in sorted(poly.items())]
    for mask in range(1,2**len(pairs)):
        weights=[{} for _ in range(dimension)];S={};ids=[]
        for ident,(i,j) in enumerate(pairs):
            if not mask&(1<<ident):continue
            ids.append(ident)
            # s=d_j-d_i; W_i=s*d_j and W_j=-s*d_i.
            add(weights[i],[j,j],1);add(weights[i],[i,j],-1)
            add(weights[j],[i,i],1);add(weights[j],[i,j],-1)
            add(S,[i,i],1);add(S,[i,j],-2);add(S,[j,j],1)
        candidates.append(dict(id=mask-1,basis_ids=ids,active_coordinates=[i for i,w in enumerate(weights) if w],
            weights=list(map(encoded,weights)),normalizer=encoded(S),sos_linear_forms=[basis[i]['sum'] for i in ids],
            normalizer_nonnegative_proved=True,normalizer_positive_proved=False))
    return dict(schema='core-cutoff-frame-v1',dimension=dimension,constraint_rank=dimension*(dimension+1)-len(pairs),
                basis=basis,candidates=candidates,whole_signed_bound_proved=False,RH_proved=False,
                weak_fact_countermodel=dict(drifts=['1']*dimension,normalizer='0',
                    scope='upper magnitude bounds alone cannot prove the recovery denominator positive',actual_mobius_counterexample=False),
                supplied=['polynomial degree limit','square-and-pool construction','Cauchy recovery rule'],
                generated=['complete rational nullspace','all pooled expressions','exact signed cancellation'],model_calls=0)


class CutoffFrameCheckerTests(unittest.TestCase):
    def setUp(self):ctx.prec=224

    def test_full_five_geometry_catalogue_and_nullspace_rank(self):
        result=catalogue(5);summary=CHECK.check_catalogue(result,WORK)
        self.assertEqual(summary['constraint_rank'],20)
        self.assertEqual(summary['basis_rank'],10)
        self.assertEqual(summary['candidates'],1023)
        self.assertFalse(summary['normalizer_positive_proved'])

    def test_generic_dimension_and_rank_completeness(self):
        result=catalogue(3)
        self.assertTrue(CHECK.check_catalogue(result,WORK)['exact_polynomial_identities_verified'])
        # Rank audit must reject repeated valid kernel vectors: identities alone
        # cannot establish completeness of the advertised basis.
        result['basis'][1]['vector']=deepcopy(result['basis'][0]['vector'])
        result['basis'][1]['sum']=deepcopy(result['basis'][0]['sum'])
        with self.assertRaises(ValueError):CHECK.check_catalogue(result,WORK)

    def test_basis_rank_normalization_and_coordinate_sum_tamper(self):
        for kind in ('rank','constraint','primitive','sum','nullspace'):
            bad=catalogue(3)
            if kind=='rank':bad['basis'].pop()
            if kind=='constraint':bad['constraint_rank']=8
            if kind=='primitive':
                bad['basis'][0]['vector']=[[str(2*int(c)) for c in row] for row in bad['basis'][0]['vector']]
                bad['basis'][0]['sum']=[str(2*int(c)) for c in bad['basis'][0]['sum']]
            if kind=='sum':bad['basis'][0]['sum'][0]='1'
            if kind=='nullspace':bad['basis'][0]['vector'][0][0]='1'
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.check_catalogue(bad,WORK)

    def test_pool_exhaustiveness_signed_crosses_and_SOS_tamper(self):
        for kind in ('subset','weight','normalizer','SOS','support','positive','closed'):
            bad=catalogue(3)
            if kind=='subset':bad['candidates'].pop()
            if kind=='weight':bad['candidates'][-1]['weights'][0][0]['coefficient']='2'
            if kind=='normalizer':bad['candidates'][-1]['normalizer'][0]['coefficient']='1'
            if kind=='SOS':bad['candidates'][-1]['sos_linear_forms'].pop()
            if kind=='support':bad['candidates'][-1]['active_coordinates'].pop()
            if kind=='positive':bad['candidates'][-1]['normalizer_positive_proved']=True
            if kind=='closed':bad['whole_signed_bound_proved']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.check_catalogue(bad,WORK)

    def test_weak_countermodel_and_supplied_scope_tamper(self):
        for kind in ('actual','drift','generated','model'):
            bad=catalogue(3)
            if kind=='actual':bad['weak_fact_countermodel']['actual_mobius_counterexample']=True
            if kind=='drift':bad['weak_fact_countermodel']['drifts'][0]='0'
            if kind=='generated':bad['generated'].append('RH proof')
            if kind=='model':bad['model_calls']=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.check_catalogue(bad,WORK)

    def test_expanded_frame_weights_and_negative_recovery(self):
        result=catalogue(3);candidate=result['candidates'][-1]
        value=CHECK.evaluate(candidate,result['basis'],list(map(arb,[1,2,3])),[(1,1),(2,2),(3,3)],WORK)
        self.assertEqual(value['status'],'certified_positive')
        self.assertTrue(value['normalizer'].contains(6))
        for got,expected in zip(value['weights'],[8,2,-4]):self.assertTrue(got.contains(expected))
        self.assertTrue((value['K']-arb(7)/3).contains(0))
        self.assertTrue(value['lambda'][2]<0)

    def test_aliases_certify_singularity_before_interval_evaluation(self):
        result=catalogue(3);candidate=result['candidates'][-1]
        drifts=[arb('1 +/- 0.01')]*3
        value=CHECK.evaluate(candidate,result['basis'],drifts,[(7,11)]*3,WORK)
        self.assertEqual(value['status'],'exact_singular')
        self.assertIsNone(value['K'])
        self.assertEqual(value['normalizer'],0)
        self.assertTrue(all(v==0 for v in value['weights']))

    def test_zero_containing_balls_remain_unresolved(self):
        result=catalogue(3)
        value=CHECK.evaluate(result['candidates'][-1],result['basis'],[arb('1 +/- 0.01')]*3,
                             [(1,1),(2,2),(3,3)],WORK)
        self.assertEqual(value['status'],'unresolved_positive')
        self.assertIsNone(value['lambda'])
        self.assertIsNone(value['K'])

    def test_aliases_are_not_claimed_when_intervals_disagree(self):
        result=catalogue(3)
        with self.assertRaises(ValueError):CHECK.evaluate(result['candidates'][-1],result['basis'],
            list(map(arb,[1,2,3])),[(1,1)]*3,WORK)

    def test_Abel_moments_against_independent_cube_root_sum(self):
        mu=[0,1,-1,-1,0,-1,1,-1,0,0,1,-1,0]
        requests=dict(a=[1,3,8,12],b=[1,5,8,12]);result=CHECK.moments(mu,requests,WORK)
        for name,power in [('a',2),('b',4)]:
            for cutoff in requests[name]:
                direct=arb(0)
                for n in range(1,cutoff+1):
                    direct+=mu[n]/(arb(n).root(3)**power);WORK.charge(300)
                self.assertTrue((result[name][str(cutoff)]-direct).contains(0))
        self.assertEqual(result['effective_cutoffs'],{'1':1,'3':3,'5':5,'8':7,'12':11})
        self.assertEqual(result['a']['1'],1)
        self.assertEqual(result['b']['1'],1)

    def test_complete_inverse_unit_and_prime_power_validation(self):
        mu=[0,1,-1,-1,0,-1,1,-1,0,0,1,-1,0]
        for kind in ('unit','prime_power','dummy','type','length'):
            bad=mu.copy()
            if kind=='unit':bad[1]=0
            if kind=='prime_power':bad[4]=1
            if kind=='dummy':bad[0]=1
            if kind=='type':bad[6]=True
            if kind=='length':bad.pop()
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.moments(bad,dict(a=[12],b=[]),WORK)

    def test_independent_signed_source_drift_and_unsupported_c(self):
        polynomial=[dict(powers=[2,0,0,0],coefficient='27/4'),dict(powers=[1,1,0,0],coefficient='-27/4'),
                    dict(powers=[0,1,0,1],coefficient='-3/2')]
        value=CHECK.drift(polynomial,arb(2),arb(3),arb(5),WORK)
        self.assertTrue(value.contains(-36))
        for kind in ('c','duplicate','coefficient','power'):
            bad=deepcopy(polynomial)
            if kind=='c':bad[0]['powers'][2]=1
            if kind=='duplicate':bad.append(deepcopy(bad[0]))
            if kind=='coefficient':bad[0]['coefficient']='0'
            if kind=='power':bad[0]['powers'][0]=True
            with self.subTest(kind=kind),self.assertRaises(ValueError):CHECK.drift(bad,arb(2),arb(3),arb(5),WORK)

    def test_precision_request_and_rational_caps(self):
        ctx.prec=192
        with self.assertRaises(ValueError):CHECK.moments([0,1],dict(a=[1],b=[1]),WORK)
        ctx.prec=224
        for requests in [dict(a=[],b=[]),dict(a=[1,1],b=[]),dict(a=[True],b=[]),dict(a=[0],b=[]),dict(a=[1])]:
            with self.subTest(requests=requests),self.assertRaises(ValueError):CHECK.moments([0,1],requests,WORK)
        for text in ('2/4','01','+1','-0','1.0','1/0',True):
            with self.subTest(text=text),self.assertRaises(ValueError):CHECK._rational(text,WORK)
        with self.assertRaises(OverflowError):CHECK._rational('1',Meter(1))


def tearDownModule():
    print(f'SYNTHETIC_WORK module=test_check_core_cutoff_frame operations={WORK.operations} elapsed_seconds={time.monotonic()-START:.6f}')


if __name__=='__main__':
    resource.setrlimit(resource.RLIMIT_AS,(512*1024*1024,512*1024*1024))
    if len(sys.argv)>1:suite=unittest.defaultTestLoader.loadTestsFromNames(['__main__.CutoffFrameCheckerTests.'+n for n in sys.argv[1:]])
    else:suite=unittest.defaultTestLoader.loadTestsFromTestCase(CutoffFrameCheckerTests)
    outcome=unittest.TextTestRunner(verbosity=2).run(suite)
    run=dict(returncode=0 if outcome.wasSuccessful() else 1,operations=WORK.operations,tests=outcome.testsRun,
        elapsed_seconds=time.monotonic()-START,failures=len(outcome.failures),errors=len(outcome.errors),
        failure_details=[dict(test=str(t),traceback=trace) for t,trace in outcome.failures+outcome.errors])
    try:
        with open('core_cutoff_frame_checker_development.json') as source:previous=json.load(source)
    except FileNotFoundError:previous=dict(runs=[])
    runs=previous['runs']+[run]
    receipt=dict(schema='core-cutoff-frame-checker-development-v1',runs=runs,operations=sum(r['operations'] for r in runs),
        success=outcome.wasSuccessful(),peak_live_cells=WORK.peak_live_cells,maximum_rational_bits=WORK.maximum_rational_bits,
        memory_limit_bytes=512*1024*1024,operation_limit=50000000,elapsed_limit_seconds=180,
        no_source_observations=True,edits_stopped=outcome.wasSuccessful())
    with open('core_cutoff_frame_checker_development.json','w') as output:json.dump(receipt,output,indent=2);output.write('\n')
    raise SystemExit(run['returncode'])
