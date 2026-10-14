"""Synthetic integration checks for pre-score proof admission and mixtures."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import floor_residual_search_045 as S


METERS=[]


def meter(cls,**kwargs):
    result=cls(**kwargs);METERS.append(result);return result


def drift(order=2,a='1/3',theta='3/5'):
    return S.DRIFT.synthesize_mixture([str(j) for j in range(1,order+1)],a,theta,meter(S.DRIFT.Meter))


def recipe(weight,id='toy'):
    return dict(id=id,base=weight,auxiliary=None)


def rows(r):
    cache={}
    for node in S.drift_nodes(r['base']):
        cert=S.DRIFT.mixture_certificate(node,meter(S.DRIFT.Meter))
        S.DRIFT_CHECK.verify_certificate(node,cert,meter(S.DRIFT_CHECK.Meter))
        cache[S.OLD.ast_key(node)]=cert
    return S.candidate_rows(r,{},cache,meter(S.RATE.Meter),meter(S.DRIFT_CHECK.Meter),max_index=6)


class ProofGatedDriftSearch(unittest.TestCase):
    def test_independent_source_rate_for_product_and_drift(self):
        r=recipe(drift())
        candidate=rows(r)[1]
        self.assertEqual(candidate['energy_rate'],'8/5')
        product=recipe(dict(kind='product',left=r['base'],right=S.OLD.taper('log','3/7')))
        row=rows(product)[1]
        self.assertEqual(row['energy_rate'],'6/7')
        self.assertEqual(row['mu'],-1)
        self.assertEqual(row['nonzero_license']['sign'],-1)

    def test_proof_gates_reject_cutoff_and_only_overfast_drift_bounds(self):
        g=dict(recipes=[recipe(S.OLD.taper('cutoff','3/11'),'toy_cutoff'),
                        recipe(drift(order=1,theta='3/4'),'toy_drift')],
               initial_log_etas=['1/3','2/3','1'],log_costs=['1','4'])
        output=S.proof_gates(g)
        METERS.append(type('Recorded',(),{'operations':sum(output[k] for k in (
            'producer_operations','checker_operations','drift_certificate_operations','cutoff_operations','cutoff_replay_operations'))})())
        for entry in output['admissions']:
            if entry['family']=='toy_cutoff':
                self.assertFalse(entry['admitted_bounds'])
                self.assertTrue(entry['cutoff_verification']['verified'])
            else:
                self.assertTrue(entry['admitted_bounds'])
                self.assertEqual({b['eta'] for b in entry['admitted_bounds']},{'1/2','1/3'})
                self.assertFalse(entry['uniform_upper_bound_proved'])
                self.assertIsNone(entry['cutoff_verification'])
        self.assertTrue(output['all_before_new_scores']);self.assertFalse(output['RH_proved'])

    def test_forcing_step_annihilation_and_boundary_constant(self):
        rr=rows(recipe(drift(order=1,a='10',theta='1/2')))
        eligible=S.forcing_witnesses(rr,2,'1/2')
        self.assertEqual([r['index'] for r in eligible],[3,5])
        self.assertEqual(S.reject_bound(eligible,'1/64','1')['reason'],'strict_boundary_constant')
        self.assertIsNone(S.reject_bound(eligible,'10000','1'))
        self.assertIsNone(S.reject_bound(eligible,'1/64','1/2'))
        self.assertEqual(S.reject_bound(eligible,'10000','3/2')['reason'],'strict_log_rate')
        self.assertIn(2,[r['index'] for r in S.forcing_witnesses(rr,2,'0')])

    def test_exact_profile_source_and_internal_auxiliary_baseline(self):
        profile=drift(order=3,theta='2/7')
        r=recipe(dict(kind='product',left=profile,right=S.OLD.taper('cutoff','2/5')))
        c=S.Compiler(15,meter(S.OLD.Meter),meter(S.DRIFT.Meter))
        p=c.compile(r,15);base=S.baseline_recipe(r)
        self.assertEqual(len(base['base']['left']['terms']),1)
        self.assertEqual(base['base']['left']['terms'][0]['weight'],'1')
        self.assertEqual(base['base']['left']['theta'],'2/7')
        self.assertTrue(S.has_signed_auxiliary(r))
        self.assertFalse(S.has_signed_auxiliary(base))
        cm=meter(S.DRIFT_CHECK.Meter)
        coefficients={row['n']:Q(row['value']) for row in p['coefficients']}
        taper=c.weights_at(r['base']['right'],15)
        for n,w in enumerate(c.drift.profile(profile,15),2):
            verified=S.DRIFT_CHECK.verify_compilation(profile,n,15,str(w),cm)
            mu=S.RATE_CHECK.arithmetic('mu',n,cm)
            self.assertEqual(coefficients.get(n,Q(0)),-mu*Q(verified['value'])*taper[n-2])
        self.assertEqual(p['constant'],'1');self.assertEqual(p['steps'],[])

    def test_legacy_compilation_is_reused_unchanged(self):
        r=recipe(S.OLD.taper('log','1'),'toy_old')
        old=S.OLD.Compiler(9,meter(S.OLD.Meter)).compile(r,9)
        new=S.Compiler(9,meter(S.OLD.Meter),meter(S.DRIFT.Meter)).compile(r,9)
        self.assertEqual(old,new)

    def test_symbolic_rate_requires_previously_verified_moment_certificate(self):
        with self.assertRaisesRegex(ValueError,'independently admitted'):
            S.weight_correction(drift(),3,{},meter(S.RATE.Meter))

    def test_cross_formula_value_cache_preserves_constant_and_signed_weights(self):
        class FakeNorms:
            def __init__(self):self.meter=meter(S.OLD.Meter);self.calls=[]
            def price(self,programs):
                self.calls.extend(programs)
                return [dict(value=p['constant']) for p in programs]
        raw=FakeNorms();cached=S.CachedNorms(raw)
        p=S.OLD.program('first',{2:Q(1,3)})
        alias=deepcopy(p);alias['id']='other_formula'
        zero=deepcopy(p);zero['constant']='0'
        self.assertEqual(cached.price([p,alias,zero]),[{'value':'1'},{'value':'1'},{'value':'0'}])
        self.assertEqual(cached.price([alias]),[{'value':'1'}])
        self.assertEqual((cached.hits,cached.misses,len(raw.calls)),(2,2,2))
        profile=drift();r=recipe(profile)
        retained=S.Compiler(9,meter(S.OLD.Meter),meter(S.DRIFT.Meter))
        released=S.Compiler(9,meter(S.OLD.Meter),meter(S.DRIFT.Meter),retain_compilation_certificates=False)
        self.assertEqual(retained.compile(r,9),released.compile(r,9))
        self.assertFalse(released.drift.context(profile,9).cache)
        self.assertTrue(retained.drift.context(profile,9).cache)

    def test_ranking_prioritizes_exponent_and_keeps_distinct_drift_families(self):
        def row(id,eta,drift,b='1/2',cross=0):
            return dict(family=id,q=2,b=b,has_drift=drift,maximum_mixture_order=2 if drift else 0,
                observations=[dict(N=N,forcing=dict(ranking_upper_proxy=0.1)) for N in S.TRAIN_PARENTS],
                finite_log_bound=dict(A='1',eta=eta),fallback_bound=dict(A='4',eta='1/5'),
                auxiliary_signed_needed_count=cross,refinement_signed_needed_count=cross,
                worst_forcing_log_power=-1,worst_target_log_power=-1)
        values=[row('drift_fast','1',True),row('drift_slow','1/2',True,cross=3),
                row('old','1',False),row('endpoint','1',True,b='0')]
        chosen=S.select(values)
        self.assertEqual(chosen[0]['family'],'drift_fast')
        self.assertEqual(chosen[1]['family'],'drift_slow')
        changed=deepcopy(values);changed[0]['observations'][0]['N']=607
        with self.assertRaisesRegex(ValueError,'training'):
            S.select(changed)
        with self.assertRaisesRegex(ValueError,'duplicate'):
            S.select(values+[values[0]])


if __name__=='__main__':
    path=Path(__file__).with_name('floor_residual_search_045_development.json')
    if path.exists():raise SystemExit('retain development receipt; no unchanged rerun')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ProofGatedDriftSearch))
    receipt=dict(schema='drift-search-integration-v1',invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,failures=len(result.failures),
        errors=len(result.errors),elapsed_seconds=time.monotonic()-started,operations=sum(m.operations for m in METERS))],
        exposure='synthetic profiles/arithmetic up to15, artificial ranking; no actual saved candidate or new study')
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
