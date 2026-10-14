import copy
import unittest
from fractions import Fraction as Q
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

import mobius_prime_moment_075 as S
import check_mobius_prime_moment_075 as C


class Integration(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = dict(grid=80, theta=['1/2', '17/31', '7/8'], multipliers=[2, 3, 6])
        cls.data = S.make_data(cls.spec, list(range(1, 801)))

    def test_independent_source_all_phases_and_multiplicities(self):
        result = C.verify_data(self.data)
        self.assertEqual(result['status'], 'VERIFIED', result)
        self.assertEqual(result['rows_checked'], 800)
        self.assertTrue(any(any(n>1 for n in r['counts'][:2]) for r in self.data['rows']))
        bad = copy.deepcopy(self.data)
        bad['rows'][-1]['components'][0] += 1
        self.assertEqual(C.verify_data(bad)['status'], 'INVALID')

    def test_direct_cauchy_recovery_remains_conditional(self):
        rows = [r for r in self.data['rows'] if r['u']>64]
        shape = [Q(0), Q(0), Q(1, 4), Q(-1, 4), Q(0)]
        p = S.make_program(self.spec, shape, S.cauchy_beta(shape), '33/32', rows, 64, 12)
        result = C.verify_program(p, self.data)
        self.assertEqual(result['status'], 'VERIFIED_ON_FINITE_DOMAIN', result)
        self.assertTrue(result['conditional_induction_verified'])
        self.assertTrue(result['universal_direct_correlation_proved'])
        self.assertFalse(result['uniform_source_bound_proved'])
        self.assertFalse(result['RH_proved'])
        self.assertEqual(len(S.next_obligations(dict(program=p), result)), 1)

    def test_prime_correlation_counterexample_survives_valid_induction_template(self):
        rows = [r for r in self.data['rows'] if r['u']>64]
        shape, beta = [Q(0), Q(1, 10), Q(0), Q(0), Q(0)], [Q(0)]*5
        p = S.make_program(self.spec, shape, beta, '1', rows, 64)
        result = C.verify_program(p, self.data)
        self.assertEqual(result['status'], 'REFUTED')
        self.assertTrue(result['conditional_induction_verified'])
        self.assertTrue(any(w['lemma']=='correlation' for w in result['failures']))
        self.assertFalse(result['universal_direct_correlation_proved'])

    def test_invalid_negative_contraction_and_base_tampering(self):
        rows = [r for r in self.data['rows'] if r['u']>64]
        p = S.make_program(self.spec, [Q(0)]*5, [Q(0)]*5, '129/128', rows, 64)
        for key, value in [('sqrt_rho_upper', '-1'), ('base_upper', '0'), ('price_bounds', ['0']*5)]:
            bad = dict(p, **{key: value})
            self.assertEqual(C.verify_program(bad, self.data)['status'], 'INVALID')

    def test_tiny_source_and_nonvacuous_evaluation(self):
        tiny = S.make_data(self.spec, [1, 2, 3])
        self.assertEqual(C.verify_data(tiny)['status'], 'VERIFIED')
        rows = [r for r in self.data['rows'] if r['u']>64]
        p = S.make_program(self.spec, [Q(0)]*5, [Q(0)]*5, '1', rows, 64)
        self.assertEqual(C.verify_program(dict(p, training_scales=[]), self.data)['status'], 'INVALID')
        self.assertEqual(C.verify_program(p, self.data, scales=[])['status'], 'INVALID')

    def test_joint_proposals_pay_both_training_lemmas(self):
        data = dict(self.data, rows=[r for r in self.data['rows'] if r['u']>64])
        shape = [Q(0), Q(0), Q(1), Q(-1), Q(0)]
        beta = S.cauchy_beta(shape)
        record = dict(id='test', shape=list(map(str, shape)), beta=list(map(str, beta)),
                      price=str(S.dot(beta, S.price_bounds(self.spec, 64))), mode='universal_direct_cauchy',
                      origins=['synthetic_recovery'], kind='direct_only')
        found = S.propose_programs([record], data, '1', 64, 12, S.Meter())
        self.assertTrue(found['programs'])
        self.assertTrue(any('known_theorem_recovery' in p['selection']['selected_by'] for p in found['programs']))
        for item in found['programs']:
            result = C.verify_program(item['program'], data)
            self.assertEqual(result['status'], 'VERIFIED_ON_FINITE_DOMAIN', result)
            self.assertTrue(result['universal_direct_correlation_proved'])

    def test_runner_source_dependency_and_candidate_pipeline(self):
        import run_mobius_prime_moment_075 as R
        spec = dict(R.SPEC, source=self.spec, base_u=64, q=['1'], phases=[0, 1, 2],
                    discovery_k_anchors=[2, 3], adaptation_k_anchors=[4, 5])
        shape = [Q(0), Q(0), Q(1), Q(-1), Q(0)]
        task = dict(id='000', shape=list(map(str, shape)), mode='universal_direct_cauchy',
                    kind='direct_only', origins=['synthetic_recovery'])
        with tempfile.TemporaryDirectory() as tmp, patch.object(R, 'OUT', Path(tmp)), patch.object(R, 'SPEC', spec):
            parents = sorted(R.scales(spec['discovery_k_anchors'])+R.scales(spec['adaptation_k_anchors']))
            data, admitted = R.source_phase('learning', parents)
            with self.assertRaises(ValueError):
                R.require_admitted_source(data, dict(admitted, source_admission=dict(status='INVALID')))
            with self.assertRaises(ValueError):
                R.require_admitted_source(data, dict(admitted, scales=parents[:-1]))
            R.initialize_worker()
            record = R.moment_task(task)
            R.write(Path(tmp)/'moment_summary.json', dict(records=[record]))
            summary = R.candidate_task('1')
            saved = json.loads((Path(tmp)/summary['file']).read_text())
            for item in saved['programs']:
                self.assertTrue(item['discovery_admission']['conditional_induction_verified'])
                self.assertEqual(item['final_eligible'], item['adaptation']['status']=='VERIFIED_ON_FINITE_DOMAIN')


if __name__ == '__main__':
    unittest.main()
