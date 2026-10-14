"""Synthetic integration of rate and cutoff admission; no saved candidates."""
from copy import deepcopy
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch

import publish_floor_residual_followup_044 as P


METERS = []


def meter(cls, **kwargs):
    out = cls(**kwargs)
    METERS.append(out)
    return out


class AnalyticFeedbackIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.selected = {'recipes': [
            {'id': 'toy_cutoff', 'base': {'kind':'taper','coordinate':'cutoff','alpha':'3/11','gamma':'1'}, 'auxiliary': None},
            {'id': 'toy_log', 'base': {'kind':'taper','coordinate':'log','alpha':'2/7','gamma':'1'}, 'auxiliary': None},
            {'id': 'toy_twist', 'base': {'kind':'vanishing_twist','rate':'2/5','level_power':1}, 'auxiliary': None}],
            'rules': []}
        for recipe in cls.selected['recipes']:
            cls.selected['rules'].append({'family':recipe['id'],'q':2,'b':'1/2',
                'finite_log_bound':{'A':'1','eta':'1'},'stratum':recipe['id']})
        cls.rates = P.RATE.audit_selected(cls.selected,max_index=6,meter=meter(P.RATE.Meter))
        cls.rate_verification = P.RATE_CHECK.verify(cls.selected,cls.rates,meter=meter(P.RATE_CHECK.Meter))
        cls.cutoffs = []
        for recipe, rule in zip(cls.selected['recipes'],cls.selected['rules']):
            cls.cutoffs.append(dict(rule_key=[rule['family'],rule['q'],rule['b'],rule['stratum']],
                **P.cutoff_review(P.request_for(recipe,rule['q'],rule['b']),meter(P.CUTOFF.Meter),meter(P.CUTOFF.Meter))))

    def merge(self, selected=None, rates=None, verification=None, cutoffs=None):
        return P.merge_rules(self.selected if selected is None else selected,
            self.rates if rates is None else rates,
            self.rate_verification if verification is None else verification,
            self.cutoffs if cutoffs is None else cutoffs)

    def test_end_to_end_distinct_domains_and_open_claims(self):
        cutoff, log, twist = self.merge()
        self.assertEqual(cutoff['uniform_vanishing_forcing_all_integers'],'analytically_refuted')
        self.assertEqual(cutoff['selected_eta_on_any_unbounded_subsequence'],'OPEN')
        self.assertEqual(log['uniform_vanishing_forcing_all_integers'],'OPEN')
        self.assertEqual(log['selected_eta_on_any_unbounded_subsequence'],'analytically_refuted')
        self.assertEqual(log['rate_witness']['energy_rate'],'4/7')
        self.assertEqual(twist['advertised_all_integer_bound'],'OPEN')
        for row in (cutoff,log,twist):
            self.assertEqual(row['geometric_subsequence_convergence'],'OPEN')
            self.assertFalse(row['lower_eta_is_proved'])
            self.assertTrue(row['finite_norm_inequalities_remain_true'])
            self.assertFalse(row['RH_proved']); self.assertFalse(row['RH_refuted'])

    def test_unsupported_is_retained_without_calling_proof_verifier(self):
        req=P.request_for(self.selected['recipes'][1],2,'1/2')
        with patch.object(P.CUTOFF,'verify_guard',side_effect=AssertionError('unsupported is not a proof')):
            row=P.cutoff_review(req,meter(P.CUTOFF.Meter),meter(P.CUTOFF.Meter))
        self.assertEqual(row['certificate']['status'],P.CUTOFF.UNSUPPORTED)
        self.assertFalse(row['verification']['verified'])
        self.assertFalse(row['verification']['uniform_vanishing_forcing_impossible'])

    def test_complete_rule_binding_includes_bound_parameters(self):
        changed=deepcopy(self.selected)
        changed['rules'][0]['finite_log_bound']['eta']='1/2'
        with self.assertRaisesRegex(ValueError,'complete selected rule'):
            self.merge(selected=changed)

    def test_cutoff_recipe_and_domain_cannot_be_transplanted(self):
        for field in ('recipe','domain'):
            rows=deepcopy(self.cutoffs)
            if field=='recipe': rows[0]['request']['recipe']['base']['alpha']='4/11'
            else: rows[0]['request']['domain']['kind']='geometric_subsequence'
            with self.assertRaisesRegex(ValueError,'complete selected rule'):
                self.merge(cutoffs=rows)

    def test_missing_or_duplicate_results_are_not_complete_coverage(self):
        for rows in (self.cutoffs[:-1],self.cutoffs+[self.cutoffs[0]]):
            with self.assertRaisesRegex(ValueError,'coverage'):
                self.merge(cutoffs=rows)
        rates=deepcopy(self.rates)
        rates['reviews'][0]['rule_reviews'].append(deepcopy(rates['reviews'][0]['rule_reviews'][0]))
        with self.assertRaisesRegex(ValueError,'duplicate'):
            self.merge(rates=rates)

    def test_unverified_refutation_or_supported_unsupported_mix_is_rejected(self):
        with self.assertRaisesRegex(ValueError,'independent rate replay'):
            self.merge(verification={'verified':False})
        rows=deepcopy(self.cutoffs); rows[0]['verification']['verified']=False
        with self.assertRaisesRegex(ValueError,'independent cutoff proof'):
            self.merge(cutoffs=rows)
        rows=deepcopy(self.cutoffs); rows[1]['verification']['verified']=True
        with self.assertRaisesRegex(ValueError,'unsupported cutoff'):
            self.merge(cutoffs=rows)

    def test_native_receipt_formats_and_last_run_failures(self):
        for receipt in ({'runs':[{'returncode':0}]},
                        {'invocations':[{'returncode':1},{'returncode':0}]},
                        {'invocations':1,'tests_run':11,'failures':0,'errors':0}):
            self.assertTrue(P.passing_receipt(receipt))
        for receipt in ({}, {'runs':[]}, {'runs':[{'returncode':0},{'returncode':1}]},
                        {'runs':[{'returncode':False}]}, {'invocations':1},
                        {'invocations':1,'tests_run':0,'failures':0,'errors':0},
                        {'invocations':1,'tests_run':11,'failures':1,'errors':0}):
            self.assertFalse(P.passing_receipt(receipt))


if __name__=='__main__':
    path=Path(__file__).with_name('floor_residual_followup_044_development.json')
    if path.exists():
        raise SystemExit('retain completed focused receipt; do not rerun unchanged integration')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(AnalyticFeedbackIntegration))
    receipt={'schema':'floor-followup-integration-v1','invocations':[{
        'returncode':0 if result.wasSuccessful() else 1,'tests':result.testsRun,
        'failures':len(result.failures),'errors':len(result.errors),
        'elapsed_seconds':time.monotonic()-started,'operations':sum(m.operations for m in METERS)}],
        'scope':'synthetic ASTs only; no saved candidate application, source arrays or norms'}
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
