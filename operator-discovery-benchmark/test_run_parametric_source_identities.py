import copy
import time
import unittest

import run_parametric_source_identities as R


class ParametricRunTests(unittest.TestCase):
    def test_source_statement_bound_independently(self):
        recipe = R.S.recipes()['recipes'][0]
        certificate = R.S.produce_certificate(recipe, limits=R.LIMITS, deadline=time.monotonic()+10)
        checked = R.check_certificate(recipe, certificate, time.monotonic()+10)
        self.assertTrue(checked['FORMAL_EQ_verified'])
        self.assertFalse(checked['full_target_proved'])
        changed = copy.deepcopy(recipe)
        changed['rhs'] = ['q', '0']
        with self.assertRaises(ValueError):
            R.check_certificate(changed, certificate, time.monotonic()+10)

    def test_covers_actual_prime_rowmass_and_opaque_definition_binding(self):
        recipe = R.S.recipes()['recipes'][-1]
        certificate = R.S.produce_certificate(recipe, limits=R.LIMITS, deadline=time.monotonic()+10)
        self.assertTrue(R.check_certificate(recipe, certificate, time.monotonic()+10)['FORMAL_EQ_verified'])
        changed = copy.deepcopy(certificate)
        changed['context']['functions'][0]['definition_hash'] = '0'*64
        with self.assertRaises(ValueError):
            R.check_certificate(recipe, changed, time.monotonic()+10)

    def test_budget_includes_both_independent_checks(self):
        r = R.RESOURCES
        self.assertEqual(r['total_work_reserve'], sum(r[n] for n in
                         ('producer_reserve', 'worker_checker_reserve', 'whole_audit_reserve', 'binding_io_reserve', 'test_reserve')))
        self.assertLess(r['total_work_reserve'], r['max_work'])
        self.assertEqual(r['producer_reserve'], 74*R.LIMITS['max_operations'])
        self.assertEqual(r['worker_checker_reserve'], 74*R.LIMITS['max_operations'])

    def test_no_whole_target_or_discovery_promotion(self):
        p = R.protocol(R.S.recipes())
        self.assertIn('calibration', p['mode'])
        self.assertFalse(p['source_adapter_compiler_equivalence_formally_proved'])
        for flag in R.FLAGS:
            self.assertFalse(p[flag])


if __name__ == '__main__':
    unittest.main()
