"""Focused synthetic moment/profile certificates; no norm or search data."""
from copy import deepcopy
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import sys
import time
import unittest

import floor_residual_drift_045 as drift

METERS = []


def meter(**kwargs):
    m = drift.Meter(**kwargs)
    METERS.append(m)
    return m


def general(a='1', theta='1/2'):
    return {'kind': 'drift_mixture', 'a': a, 'theta': theta,
            'terms': [{'rate': '1', 'weight': '-1'}, {'rate': '2', 'weight': '2'}]}


class DriftTests(unittest.TestCase):
    def setUp(self):
        self.meter = meter()

    def test_exact_ceiling_boundaries(self):
        for a, theta, N, ceiling, expected in [('1', '1/2', 7, 2, '2/3'),
                                             ('1', '1/2', 8, 2, '1/2'),
                                             ('3/2', '1/2', 15, 3, '3/4'),
                                             ('1', '1/3', 63, 2, '1/3'),
                                             ('1/257', '17/257', 2, 1, '1/2')]:
            b = drift.beta_certificate(a, theta, N, self.meter)
            self.assertEqual(b['ceiling'], str(ceiling))
            self.assertEqual(b['beta'], expected)
            aa, tt, L = Q(a), Q(theta), N.bit_length()
            right = aa.numerator**tt.denominator*L**tt.numerator
            self.assertLess((ceiling-1)**tt.denominator*aa.denominator**tt.denominator, right)
            self.assertLessEqual(right, ceiling**tt.denominator*aa.denominator**tt.denominator)
            self.assertEqual(drift.beta(a, theta, N, self.meter), Q(expected))

    def test_general_rate_set_exact_gaussian_moments(self):
        rates = ['7/3', '1/7', '2/5']
        spec = drift.synthesize_mixture(rates, a='3/7', theta='2/9', meter=self.meter)
        self.assertEqual([row['rate'] for row in spec['terms']], ['1/7', '2/5', '7/3'])
        cert = drift.mixture_certificate(spec, self.meter)
        self.assertEqual(cert['order'], 3)
        self.assertEqual([row['value'] for row in cert['moments'][:3]], ['1', '0', '0'])
        product = math.prod(Q(r) for r in rates)
        self.assertEqual(Q(cert['leading_moment']), product)
        self.assertEqual(cert['coefficient_rate'], '7/3')
        self.assertEqual(cert['energy_rate'], '14/3')
        self.assertEqual(Q(cert['leading_error_coefficient']['rational']), product*Q(3, 7)**3/6)
        self.assertEqual(cert['leading_error_coefficient']['log_n_power'], '3')

    def test_one_through_eight_terms_generated_not_bank(self):
        for size in range(1, 9):
            spec = drift.synthesize_mixture([str(Q(2*j+1, 13)) for j in range(size)], meter=self.meter)
            cert = drift.mixture_certificate(spec, self.meter)
            self.assertEqual(cert['order'], size)
            self.assertEqual(cert['vanishing_orders'], list(range(1, size)))
            product = math.prod(Q(t['rate']) for t in spec['terms'])
            self.assertEqual(Q(cert['leading_moment']), (-1)**(size+1)*product)
            self.assertEqual(cert['kernel_certificate']['status'], 'certified')

    def test_arbitrary_denominator_compiler(self):
        spec = drift.synthesize_mixture(['1/257'], a='2/7', theta='1/257', meter=self.meter)
        row = drift.compile_mixture(spec, 3, 7, self.meter)
        self.assertEqual(row['precision_bits'], 12)
        self.check_root_rows(row)
        self.assertGreater(self.meter.max_power_bits, 257)

    def check_root_rows(self, proposal):
        p, n = proposal['precision_bits'], proposal['n']
        total = Q(0)
        for term in proposal['terms']:
            value, exponent = Q(term['rounded_value']), Q(term['exponent'])
            D, k = 2**p, value*2**p
            self.assertEqual(k.denominator, 1)
            u, v = exponent.numerator, exponent.denominator
            self.assertLessEqual(k.numerator**v*n**u, D**v)
            self.assertLess(D**v, (k.numerator+1)**v*n**u)
            total += Q(term['weight'])*value
        self.assertEqual(Q(proposal['value']), total)

    def test_compilation_retains_signs_and_all_root_inequalities(self):
        spec = drift.synthesize_mixture(['1/3', '3/7', '2'], a='2/5', theta='2/7', meter=self.meter)
        for n, N in [(1, 17), (2, 17), (7, 31), (31, 31)]:
            proposal = drift.compilation_certificate(spec, n, N, self.meter)
            self.check_root_rows(proposal)
            self.assertTrue(proposal['signs_retained'])
            self.assertIsNone(proposal['exact_rounded_range_claim'])
            self.assertEqual(drift.mixture_value(spec, n, N, self.meter), Q(proposal['value']))

    def test_exact_rational_roots(self):
        spec = drift.synthesize_mixture(['1'], meter=self.meter)
        self.assertEqual(drift.mixture_value(spec, 16, 15, self.meter), Q(1, 4))
        self.assertEqual(drift.mixture_value(spec, 1, 15, self.meter), 1)

    def test_general_signed_mixture_not_positive(self):
        cert = drift.mixture_certificate(general(), self.meter)
        self.assertEqual(cert['order'], 1)
        self.assertEqual(cert['leading_moment'], '3')
        self.assertEqual(cert['kernel_certificate']['status'], 'NOT_CERTIFIED')
        self.assertIsNone(cert['kernel_certificate']['raw_range'])
        self.assertEqual(drift.mixture_value(general(), 16, 15, self.meter), Q(-1, 8))
        self.assertFalse(cert['whole_signed_norm_proved'])
        self.assertFalse(cert['norm_convergence_proved'])

    def test_polynomial_kernel_identity_independent_product(self):
        spec = drift.synthesize_mixture(['1/7', '3/5', '11/3'], meter=self.meter)
        cert = drift.kernel_certificate(spec, self.meter)
        num = [Q(x) for x in cert['numerator_polynomial_ascending']]
        den = [Q(x) for x in cert['denominator_polynomial_ascending']]
        rr, ww = [Q(t['rate']) for t in spec['terms']], [Q(t['weight']) for t in spec['terms']]
        for s in (Q(0), Q(1, 3), Q(7)):
            self.assertEqual(sum(w*r/(s+r) for w, r in zip(ww, rr)), math.prod(r/(s+r) for r in rr))
            self.assertEqual(sum(c*s**k for k, c in enumerate(num))/sum(c*s**k for k, c in enumerate(den)),
                             math.prod(r/(s+r) for r in rr))
        self.assertEqual(num, [math.prod(rr), Q(0), Q(0)])
        self.assertEqual(cert['raw_range'], ['0', '1'])
        self.assertFalse(cert['rounded_range_proved'])

    def test_kernel_certificate_rejects_normalized_perturbation(self):
        spec = drift.synthesize_mixture(['1', '2', '5/2'], meter=self.meter)
        spec['terms'][0]['weight'] = str(Q(spec['terms'][0]['weight'])+Q(1, 7))
        spec['terms'][1]['weight'] = str(Q(spec['terms'][1]['weight'])-Q(1, 7))
        self.assertEqual(drift.kernel_certificate(spec, self.meter)['status'], 'NOT_CERTIFIED')
        self.assertEqual(drift.mixture_certificate(spec, self.meter)['order'], 1)

    def test_finite_scalar_bound_pays_rounding(self):
        specs = [general(), drift.synthesize_mixture(['1', '3/2', '5'], meter=self.meter)]
        for spec in specs:
            for n in (1, 2, 7, 16):
                bound = drift.coefficient_error_bound(spec, n, 15, self.meter)
                value = drift.mixture_value(spec, n, 15, self.meter)
                self.assertLessEqual(abs(1-value), Q(bound['total_error_bound']))
                self.assertEqual(Q(bound['total_error_bound']), Q(bound['raw_error_bound'])+Q(bound['rounding_error_bound']))
                self.assertEqual(bound['log_upper_bound'], str((n-1).bit_length()))
                self.assertFalse(bound['whole_signed_norm_proved'])
                if n == 1:
                    self.assertEqual(bound['total_error_bound'], '0')
                elif bound['simplex_error_bound'] is not None:
                    self.assertLessEqual(Q(bound['raw_error_bound']), 1)
                    self.assertLess(Q(bound['simplex_error_bound']), Q(bound['taylor_error_bound']))

    def test_context_reuses_beta_and_cached_roots(self):
        spec = drift.synthesize_mixture(['1/3', '4/5'], meter=self.meter)
        compiler = drift.DriftCompiler(self.meter)
        context = compiler.context(spec, 15)
        before = self.meter.ceil_comparisons
        context.value(3)
        comparisons = self.meter.root_comparisons
        self.assertEqual(context.value(3), Q(context.compile(3)['value']))
        self.assertEqual(self.meter.root_comparisons, comparisons)
        context.value(4)
        self.assertEqual(self.meter.ceil_comparisons, before)
        self.assertIs(compiler.context(deepcopy(spec), 15), context)
        spec['a'] = '2'
        self.assertEqual(context.spec['a'], '1')
        self.assertIsNot(compiler.context(spec, 15), context)
        small = drift.CompilationContext(general(), 3, self.meter)
        self.assertEqual(small.profile(), (small.value(2), small.value(3)))

    def test_new_shared_atoms_across_distinct_drift_recipes(self):
        # For N15,L4, both drift prescriptions have beta1/2 and p16.
        first = drift.synthesize_mixture(['1', '2'], a='1', theta='1/2', meter=self.meter)
        second = drift.synthesize_mixture(['1', '2'], a='1', theta='1/3', meter=self.meter)
        compiler = drift.DriftCompiler(self.meter)
        left, right = compiler.context(first, 15), compiler.context(second, 15)
        self.assertIsNot(left, right)
        self.assertEqual(left.beta_certificate['beta'], right.beta_certificate['beta'])
        value = left.value(7)
        before = self.meter.root_comparisons
        self.assertEqual(right.value(7), value)
        self.assertEqual(self.meter.root_comparisons, before)
        self.assertEqual(self.meter.root_cache_hits, 2)
        self.assertEqual(len(compiler.atom_cache), 2)
        # Weights and profile identities remain different while atoms coincide.
        changed = general(a='1', theta='1/3')
        other = compiler.context(changed, 15)
        other_value = other.value(7)
        self.assertNotEqual(other_value, value)
        self.assertEqual(self.meter.root_comparisons, before)
        self.assertEqual(self.meter.root_cache_hits, 4)
        self.check_root_rows(other.compile(7))

    def test_invalid_grammar_and_cost_not_denominator_whitelist(self):
        for bad in ([], ['1', '1'], ['0'], ['-1'], ['2/6'], ['1']*9):
            with self.assertRaises(ValueError):
                drift.synthesize_mixture(bad, meter=self.meter)
        for a, theta in [('0', '1/2'), ('1', '0'), ('1', '1'), ('-1', '1/257')]:
            with self.assertRaises(ValueError):
                drift.beta(a, theta, 7, self.meter)
        for N in (True, 1):
            with self.assertRaises(ValueError):
                drift.beta('1', '1/2', N, self.meter)
        bad = general()
        bad['terms'][0]['weight'] = '1'
        with self.assertRaises(ValueError):
            drift.mixture_certificate(bad, self.meter)
        with self.assertRaises(OverflowError):
            drift.beta('1', '1/1000001', 7, self.meter)
        with self.assertRaises(OverflowError):
            drift.synthesize_mixture(['1'], meter=meter(cap=0))
        with self.assertRaises(OverflowError):
            drift.CompilationContext(general(), 1_048_577, self.meter).profile()


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromNames(sys.argv[1:], DriftTests) if len(sys.argv) > 1 else unittest.defaultTestLoader.loadTestsFromTestCase(DriftTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    invocation = {'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
                  'failures': len(result.failures), 'errors': len(result.errors),
                  'elapsed_seconds': time.monotonic()-started,
                  'operations': sum(m.operations for m in METERS),
                  'max_power_bits': max((m.max_power_bits for m in METERS), default=0),
                  'root_comparisons': sum(m.root_comparisons for m in METERS),
                  'ceil_comparisons': sum(m.ceil_comparisons for m in METERS),
                  'root_cache_hits': sum(m.root_cache_hits for m in METERS),
                  'selected_tests': sys.argv[1:] if len(sys.argv) > 1 else 'all tests existing at this invocation',
                  'exposure': 'synthetic rational rate sets, moments, polynomial identities and coefficient values only'}
    path = Path(__file__).with_name('floor_residual_drift_045_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else {
        'schema': 'floor-drift-development-v1', 'invocations': [],
        'actual_search_or_selected_application': False, 'additional_norms_evaluated': False,
        'source_arrays_read': False, 'frozen_files_modified': False,
        'old_suites_or_studies_rerun': False, 'hashes_generated': False}
    receipt['invocations'].append(invocation)
    receipt['cumulative_operations'] = sum(x['operations'] for x in receipt['invocations'])
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(invocation['returncode'])
