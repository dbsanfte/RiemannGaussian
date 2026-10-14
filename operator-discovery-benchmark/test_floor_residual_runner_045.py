"""Toy source/refinement/argument integration; no registered final supports."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch

import run_floor_residual_045 as R


WORK=[]


class DriftRunnerIntegration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        m=R.S.DRIFT.Meter()
        profile=R.S.DRIFT.synthesize_mixture(['1','5/3'],'2/7','3/7',m)
        WORK.append(m.operations)
        cls.recipe=dict(id='toy_final',base=profile,auxiliary=None)
        cls.selection=dict(stratum='toy',family='toy_final',q=2,b='1/2',
            finite_log_bound=dict(A='1',eta='1/2'),audit_log_bound=dict(A='1',eta='1/2'))
        search=dict(selected_recipes=[cls.recipe],selections=[cls.selection])
        with patch.object(R.S,'FINAL_PARENTS',(7,11,13)):
            cls.batch=R.compile_batch(search,(7,11,13))
        WORK.extend([cls.batch['compiler_counts']['operations'],cls.batch['drift_counts']['operations'],
                     cls.batch['source_replay_operations'],cls.batch['argument_operations']])

    def test_source_replayed_before_norms_and_exact_signed_refinement(self):
        self.assertTrue(self.batch['all_compiled_before_norms'])
        self.assertEqual(len(self.batch['cases']),3)
        self.assertFalse(self.batch['uniform_bound_proved'])
        for row in self.batch['source_checks']:
            self.assertEqual(row['status'],'verified_actual_mu_and_exact_drift')
        for identity in self.batch['identities']:
            self.assertTrue(identity['refinement']['verified'])
            self.assertEqual(identity['auxiliary_program']['constant'],'0')
            self.assertFalse(identity['auxiliary_program']['steps'])
        for case in self.batch['cases']:
            self.assertTrue(case['has_auxiliary'])
            self.assertLessEqual(Q(case['log_bound']['lower']),Q(case['log_bound']['upper']))

    def test_changed_mu_or_weight_is_rejected_by_source_replay(self):
        compiler=R.S.Compiler(9)
        p=compiler.compile(self.recipe,9)
        changed=deepcopy(p);changed['coefficients'][0]['value']=str(Q(changed['coefficients'][0]['value'])+1)
        meter=R.S.DRIFT_CHECK.Meter()
        with self.assertRaisesRegex(ValueError,'source-bound drift'):
            R.replay_drift_sources(compiler,self.recipe,9,changed,{},meter)
        WORK.extend([compiler.meter.operations,compiler.drift_meter.operations,meter.operations])

    def test_global_argument_queue_keeps_all_unpaid_leaves_and_exact_budgets(self):
        queue=R.argument_queue(self.batch['rules'])
        WORK.extend([queue['operations'],queue['replay_operations']])
        row=queue['rows'][0]
        self.assertTrue(row['verification']['verified'])
        self.assertEqual(row['certificate']['harmonic_level_envelope']['status'],'EXPLICIT_CONDITIONAL_LEVEL_THRESHOLD')
        self.assertGreater(queue['allocation_count'],1)
        for argument in row['bound_arguments']:
            self.assertFalse(argument['uniform_forcing_bound_proved'])
            self.assertEqual(argument['constant_recomposition'],'1')
            weights=[Q(p['young_weight']) for p in argument['premises']]
            self.assertEqual(sum(weights),1)
            self.assertEqual({p['status'] for p in argument['premises']},{'OPEN_ALL_DOMAIN_BUDGET'})
            self.assertEqual(sum(Q(p['energy_upper_constant'])/w for p,w in zip(argument['premises'],weights)),1)
        self.assertFalse(queue['RH_proved'])


if __name__=='__main__':
    path=Path(__file__).with_name('floor_residual_runner_045_development.json')
    if path.exists():raise SystemExit('retain existing integration receipt')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(DriftRunnerIntegration))
    receipt=dict(schema='drift-runner-integration-v1',invocations=[dict(returncode=0 if result.wasSuccessful() else 1,
        tests=result.testsRun,failures=len(result.failures),errors=len(result.errors),
        elapsed_seconds=time.monotonic()-started,operations=sum(WORK))],
        scope='synthetic source programs at7,11,13 and symbolic allocations; no final supports or norms')
    path.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
