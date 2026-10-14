"""Synthetic ranking/partition tests; no real candidate selection or norms."""
from copy import deepcopy
import json
from pathlib import Path
import time
import unittest
import run_floor_residual_prime_promotion_048 as P


def row(identifier,helpful,rho,tau='1',failures=0):
    return dict(id=identifier,helpful_auxiliary_count=helpful,tau=tau,
        finite_failure_count=failures,complexity=4,
        training_parents=list(P.PRIOR.S.TRAIN_PARENTS),final_observations_used=False,
        request=dict(target=dict(A='1',eta='2/7'),argument=dict(recurrence=dict(rho=rho))))


class PromotionTests(unittest.TestCase):
    def test_auxiliary_contribution_precedes_a_smaller_contraction_number(self):
        rows=[row('small_rho',0,'1/4'),row('helpful',6,'3/4'),
              row('failed',6,'1/4',failures=1),row('endpoint',6,'1/4',tau='0')]
        selected=P.promote(rows)
        self.assertEqual(selected['id'],'helpful')
        selected['request']['target']['A']='2'
        self.assertEqual(rows[1]['request']['target']['A'],'1')
        self.assertIsNone(P.promote([rows[0],rows[2],rows[3]]))

    def test_final_observations_cannot_choose_new_candidate_and_fresh_runner_is_isolated(self):
        r=row('toy',1,'1/2');r['final_observations_used']=True
        with self.assertRaises(ValueError):P.promote([r])
        runner=P.configured_runner()
        self.assertEqual(runner.S.FINAL_PARENTS,P.FRESH_PARENTS)
        self.assertEqual(P.PRIOR.S.FINAL_PARENTS,(131,167,199))
        self.assertFalse(set(runner.S.levels(P.FRESH_PARENTS))&set(P.PRIOR.S.levels(P.PRIOR.S.FINAL_PARENTS)))


if __name__=='__main__':
    path=Path(__file__).with_name('floor_residual_prime_promotion_048_development.json')
    if path.exists():raise SystemExit('preserve development receipt')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(PromotionTests))
    receipt=dict(schema='prime-promotion-development-v1',invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),seconds=time.monotonic()-started)],
        actual_candidates_or_norms_evaluated=False)
    path.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
    raise SystemExit(0 if result.wasSuccessful() else 1)
