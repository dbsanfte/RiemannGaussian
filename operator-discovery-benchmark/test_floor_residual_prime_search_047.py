"""Focused synthetic integration; no selected source arrays or search scores."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import floor_residual_prime_search_047 as S
import run_floor_residual_prime_047 as R

OPERATIONS = []


class PrimeSearchIntegration(unittest.TestCase):
    def recipe(self):
        return dict(id='synthetic', auxiliary=None,
            base=dict(kind='drift_mixture', a='1', theta='7/11',
                      terms=[dict(rate='1', weight='2'), dict(rate='2', weight='-1')]))

    def request(self):
        return S.argument_request(self.recipe(), 3, '1/4', '2',
                                  dict(A='1', eta='2/11'), '1/2', '1/4')

    def test_whole_rate_gate_precedes_catalog_and_retains_admissible_unknowns(self):
        frozen=dict(recipes=[self.recipe()], primes=[3],
            positive_exponent_factors=['1', '1/2'], bound_constants=['1'])
        result=S.proof_gates(frozen)
        OPERATIONS.append(sum(result['operations'].values()))
        row=result['admissions'][0]
        self.assertEqual([x['bound']['eta'] for x in row['rejected']], ['1'])
        self.assertEqual({x['bound']['eta'] for x in row['accepted']}, {'4/11','2/11'})
        self.assertTrue(result['before_new_scores'])
        self.assertFalse(row['upper_bound_proved'])
        self.assertEqual(row['rejected'][0]['rejection']['reason'], 'whole_norm_global_rate_obstruction')

    def test_signed_potential_formula_preserves_cross_terms(self):
        # H=(2,1), A=(-1,3), h=(1,4) in a two-dimensional real Hilbert space.
        norms={k:(Q(v),Q(v)) for k,v in dict(h=17,H=5,A=10).items()}
        self.assertEqual(S.potential_interval('1/4','-1',norms),(Q(117,4),Q(117,4)))
        self.assertEqual(S.potential_interval('1/4','2',norms),(Q(81,4),Q(81,4)))
        uncertain={k:(lo-Q(1,100),hi+Q(1,100)) for k,(lo,hi) in norms.items()}
        lo,hi=S.potential_interval('1/4','2',uncertain)
        self.assertLess(lo,Q(81,4));self.assertGreater(hi,Q(81,4))

    def test_independent_implication_check_rejects_fake_payment(self):
        request=self.request(); certificate=R.ARG.evaluate_argument(request)
        self.assertTrue(S.induction_possible(request))
        self.assertTrue(R.independent_algebra(request,certificate)['verified'])
        changed=deepcopy(certificate);changed['dependencies'][-1]['status']='PAID'
        with self.assertRaises(ValueError):R.independent_algebra(request,changed)
        bad=deepcopy(request);bad['argument']['gram']=[['1','0'],['0','0']]
        forged=deepcopy(certificate);forged['request']=bad
        with self.assertRaises(ValueError):R.independent_algebra(bad,forged)
        bad=deepcopy(request);bad['argument']['recurrence']['rho']='9/10'
        self.assertFalse(S.induction_possible(bad))

    def test_both_parities_and_final_partition_are_not_training_evidence(self):
        request=self.request(); certificate=R.ARG.evaluate_argument(request)
        bad=deepcopy(request);bad['argument']['recurrence']['parities']=[0]
        forged=deepcopy(certificate);forged['request']=bad
        with self.assertRaises(ValueError):R.independent_algebra(bad,forged)
        with self.assertRaises(ValueError):S.select([dict(training_parents=list(S.FINAL_PARENTS),final_observations_used=True)])
        self.assertEqual(S.levels([5]),[5,10,11])

    def test_argument_catalog_refuses_unpayable_induction_budget(self):
        frozen=dict(recipes=[self.recipe()],tau_values=['1/4'],d_values=['2'],
            recurrence_rho_values=['1/2','9/10'],recurrence_C_over_A_values=['1/4'])
        gates=dict(admissions=[dict(family='synthetic',prime=3,
            accepted=[dict(bound=dict(A='1',eta='2/11'))])])
        result=S.argument_catalog(frozen,gates)
        self.assertEqual(result['invalid_induction_parameters'],2)
        self.assertEqual(len(result['rows']),2)
        self.assertFalse(result['scores_evaluated'])
        self.assertEqual(sum(r['target_collinear_control'] for r in result['rows']),1)


if __name__=='__main__':
    path=Path(__file__).with_name('floor_residual_prime_search_047_development.json')
    if path.exists():raise SystemExit('preserve focused integration receipt')
    started=time.monotonic()
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(PrimeSearchIntegration))
    receipt=dict(schema='prime-search-integration-047-v1',invocations=[dict(
        returncode=0 if result.wasSuccessful() else 1,tests=result.testsRun,
        failures=len(result.failures),errors=len(result.errors),elapsed_seconds=time.monotonic()-started,
        operations=sum(OPERATIONS))],scope='synthetic gate/identity/implication/partition tests; no actual scientific arrays or scores')
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt),flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
