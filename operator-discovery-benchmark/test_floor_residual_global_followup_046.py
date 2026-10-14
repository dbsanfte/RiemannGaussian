"""Only toy protocol/certificate integration; no saved selected applications."""
from copy import deepcopy
import json
from pathlib import Path
import time
import unittest

import publish_floor_residual_global_followup_046 as P

WORK=[]


class GlobalFollowupTests(unittest.TestCase):
    def setUp(self):
        self.recipe=dict(id='toy_followup',auxiliary=None,
            base=dict(kind='drift_mixture',a='2/7',theta='3/5',terms=[dict(rate='1',weight='1')]))
        self.rule=dict(id='toy_rule',family='toy_followup',recipe=self.recipe,q=3,b='1/2',
                       audit_log_bound=dict(A='2/3',eta='3/4'))
        self.meter=P.G.Meter(cap=1_000_000)
        self.checker=P.CHECK.Meter(cap=1_000_000)

    def tearDown(self):
        WORK.extend([self.meter.operations,self.checker.operations])

    def test_finite_success_survives_but_global_claim_is_retired(self):
        cases=[dict(rule='toy_rule',N=7,logarithmic_forcing_status='verified_at_this_support')]
        row=P.review_rule(self.rule,cases,self.meter,self.checker,minimum=5)
        self.assertEqual(row['rejection_reason'],'global_rate_obstruction')
        self.assertEqual(row['finite_cases'],cases)
        self.assertTrue(row['verification']['verified'])
        self.assertEqual(row['convergence_of_profile'],'OPEN')
        self.assertFalse(row['lower_rates_proved'])
        self.assertEqual(row['all_unbounded_geometric_chains_at_this_rate'],'refuted')

    def test_boundary_stays_open_and_finite_counterexample_has_correct_scope(self):
        rule=deepcopy(self.rule);rule['audit_log_bound']['eta']='2/5'
        row=P.review_rule(rule,[],self.meter,self.checker,minimum=5)
        self.assertEqual(row['advertised_all_integer_bound'],'OPEN')
        cases=[dict(rule='toy_rule',N=11,logarithmic_forcing_status='refuted_at_this_support')]
        row=P.review_rule(rule,cases,self.meter,self.checker,minimum=5)
        self.assertEqual(row['rejection_reason'],'finite_counterexample')
        self.assertEqual(row['all_unbounded_geometric_chains_at_this_rate'],'OPEN')
        with self.assertRaises(ValueError):
            P.review_rule(rule,[dict(rule='wrong',N=11,logarithmic_forcing_status='refuted_at_this_support')],
                          self.meter,self.checker,minimum=5)

    def test_frontier_keeps_half_theta_and_taper_outside_licensed_scope(self):
        half=deepcopy(self.recipe);half['id']='toy_half';half['base']['theta']='1/2'
        product=deepcopy(self.recipe);product['id']='toy_product'
        product['base']=dict(kind='product',left=product['base'],right=dict(kind='unit'))
        rows=P.frontier([self.recipe,half,product],self.meter,self.checker)
        self.assertEqual(len(rows),2)
        self.assertEqual(rows[0]['future_rate_ceiling'],'2/5')
        self.assertIsNone(rows[1]['future_rate_ceiling'])
        self.assertFalse(any(row['any_upper_bound_proved'] for row in rows))


if __name__=='__main__':
    path=Path(__file__).with_name('floor_residual_global_followup_046_development.json')
    if path.exists():raise SystemExit('preserve existing integration receipt')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(GlobalFollowupTests))
    receipt=dict(schema='global-moving-followup-integration-v1',invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),
        elapsed_seconds=time.monotonic()-started,operations=sum(WORK))],
        scope='toy requests and artificial finite statuses; no actual source, norms or selected application')
    path.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
