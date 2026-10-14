"""Selection, interval persistence, and independent-output failure semantics."""
from copy import deepcopy
import tempfile
from pathlib import Path
import unittest
from unittest.mock import patch
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_cutoff_frame as P
import run_core_cutoff_frame as R

M = Meter(10000000, 180)


def tearDownModule():
    print('SYNTHETIC_WORK module=test_run_core_cutoff_frame operations='+str(M.operations))


def fixture(K='1', status='certified_positive'):
    return dict(requests=dict(a=[1], b=[1]), R_u='1',
        moments=dict(a={'1': '1'}, b={'1': '1'}, effective_cutoffs={'1': 1}),
        observations=[dict(X=1, N=3, cutoffs=[[1, 1], [1, 2]], aliases=[[1, 1], [1, 2]],
            drifts=['1', '2'], candidates=[dict(id=0, status=status, normalizer='1', weights=['2', '-1'],
                K=K, **{'lambda': ['2', '-1'] if K is not None else None})])])


class FrameRunnerTests(unittest.TestCase):
    def setUp(self):
        ctx.prec = 224

    def compare(self, a, b):
        with tempfile.TemporaryDirectory() as tmp, patch.object(R, 'OUT', Path(tmp)):
            R.write(Path(tmp)/'discovery-producer.json', a)
            R.write(Path(tmp)/'discovery-checker.json', b)
            return R.compare('discovery', M)

    def test_wide_finite_recovery_is_saved_as_unresolved(self):
        out = self.compare(fixture('1 +/- 0.01'), fixture('1 +/- 0.001'))
        self.assertEqual(out['observations'][0]['candidates'][0]['status'], 'unresolved_wide')
        self.assertFalse(out['whole_signed_bound_proved'])
        value = arb('1 +/- 0.01')
        restored = arb(R.serial(value))
        self.assertTrue(restored.overlaps(value))
        self.assertFalse(R.tight(restored))

    def test_independent_disagreement_and_missing_candidate_rejected(self):
        with self.assertRaises(ArithmeticError):
            self.compare(fixture('1'), fixture('2'))
        bad = fixture()
        bad['observations'][0]['candidates'].clear()
        with self.assertRaises(ValueError):
            self.compare(fixture(), bad)

    def test_singularity_requires_agreement_and_never_gets_a_cost(self):
        a = fixture(None, 'exact_singular')
        out = self.compare(a, deepcopy(a))
        result = out['observations'][0]['candidates'][0]
        self.assertEqual(result['status'], 'exact_singular')
        self.assertIsNone(result['K'])
        b = deepcopy(a)
        b['observations'][0]['candidates'][0]['status'] = 'unresolved_positive'
        with self.assertRaises(ArithmeticError):
            self.compare(a, b)

    def test_singular_candidate_retained_without_being_ranked_as_a_success(self):
        catalogue = P.catalogue(2, M)
        geometries = [dict(all_finite_head_remainders_paid=True)]*2
        observations = [dict(X=1, candidates=[dict(id=0, status='exact_singular', K=None)]),
                        dict(X=2, candidates=[dict(id=0, status='certified_positive', K='5')])]
        out = R.select(catalogue, observations, geometries, M)
        self.assertEqual(out['selected'], [dict(id=0, route='all_centered_finite_heads_paid')])
        self.assertFalse(out['rankings'][0]['finite_nonsingular'])
        self.assertIsNone(out['rankings'][0]['worst_observed_doubling_exponent'])
        self.assertFalse(out['evaluation_read'])

    def test_selector_uses_discovery_growth_and_preserves_independent_supports(self):
        catalogue = P.catalogue(3, M)
        geometries = [dict(all_finite_head_remainders_paid=i < 2) for i in range(3)]
        observations = [dict(X=X, candidates=[dict(id=c['id'], status='certified_positive', K=str(X**(c['id']+1)))
                        for c in catalogue['candidates']]) for X in (1, 2)]
        with patch.object(R, 'read', side_effect=AssertionError('selector must not read evaluation files')):
            out = R.select(catalogue, observations, geometries, M)
        self.assertEqual({v['route'] for v in out['selected']}, {'recovery_conditioning_support_2',
                         'recovery_conditioning_support_3', 'all_centered_finite_heads_paid'})
        self.assertFalse(out['evaluation_read'])
        self.assertFalse(out['constants_fitted'])


if __name__ == '__main__':
    unittest.main()
