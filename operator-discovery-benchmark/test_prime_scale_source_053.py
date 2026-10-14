"""Small synthetic source fixtures only; no pilot arrays or old suite replay."""
from dataclasses import FrozenInstanceError, replace
from fractions import Fraction as Q
import json
import math
import pickle
from pathlib import Path
import time
import unittest
from unittest.mock import patch
import numpy as np
from flint import arb, ctx

import prime_scale_source_053 as S

METERS = []


def meter(**kwargs):
    result = S.Meter(**kwargs)
    METERS.append(result)
    return result


def trial_mu(n, work):
    if n == 0:
        return 0
    remaining, distinct, candidate = n, 0, 2
    while candidate*candidate <= remaining:
        work.charge(8+remaining.bit_length())
        if remaining % candidate == 0:
            remaining //= candidate
            distinct += 1
            if remaining % candidate == 0:
                return 0
        candidate += 1
    return (-1)**(distinct+(remaining > 1))


def exact_endpoint(value):
    n, e = value.man_exp()
    n, e = int(n), int(e)
    return Q(n << e) if e >= 0 else Q(n, 1 << -e)


def direct_unrounded(alpha, N, work):
    with ctx.workprec(256):
        exponent = arb(Q(alpha).numerator)/Q(alpha).denominator
        result = arb(0)
        for d in range(2, N+1):
            mu = trial_mu(d, work)
            if mu:
                # Different local representation: exp(alpha*log(log d)).
                atom = (exponent*arb(d).log().log()).exp()
                result -= mu*(N//d)*atom
                work.charge(64+256*256)
        return exact_endpoint(result.lower()), exact_endpoint(result.upper())


class SourceTests(unittest.TestCase):
    def test_exact_mu_sieve_against_trial_factorization_and_primepowers(self):
        work = meter()
        mu = S._sieve_mu(120, work)
        self.assertEqual(mu.dtype, np.int8)
        for n in range(121):
            self.assertEqual(int(mu[n]), trial_mu(n, work))
        self.assertEqual(int(mu[1]), 1)
        self.assertEqual(int(mu[30]), -1)
        self.assertEqual(int(mu[36]), 0)
        self.assertGreater(work.primitives['sieve_square_zero_entries'], 0)

    def test_quantized_atoms_and_exact_prefix_storage(self):
        work = meter()
        source = S.make_source('1/2', 64, bits=12, meter=work)
        for array in (source.prefix_w, source.prefix_up, source.prefix_down):
            self.assertEqual(array.dtype, np.int64)
            self.assertFalse(array.flags.writeable)
            self.assertEqual(array.shape, (65,))
        self.assertFalse(source.mu.flags.writeable)
        self.assertEqual(int(source.prefix_w[1]), 0)
        with ctx.workprec(256):
            for d in range(2, 65):
                weight = int(source.prefix_w[d])-int(source.prefix_w[d-1])
                mu = trial_mu(d, work)
                if mu:
                    atom = (arb(d).log().log()/2).exp()*(1 << 12)
                    lo = exact_endpoint(atom.lower())
                    hi = exact_endpoint(atom.upper())
                    self.assertEqual(lo.numerator//lo.denominator, hi.numerator//hi.denominator)
                    self.assertEqual(weight, -mu*(lo.numerator//lo.denominator))
                    work.charge(64+256*256)
                else:
                    self.assertEqual(weight, 0)
        metadata = source.metadata()
        self.assertEqual(sum(metadata['atom_refinement_counts'].values()),
                         sum(int(source.mu[d]) != 0 for d in range(2, 65)))
        self.assertFalse(metadata['independent_source_verified_here'])
        self.assertFalse(metadata['all_scale_bound_proved'])
        self.assertFalse(metadata['artifact_hashes_used'])
        with self.assertRaises(FrozenInstanceError):
            source.bits = 14

    def test_all_small_hyperbola_queries_equal_direct_integer_sums(self):
        work = meter()
        source = S.make_source('2/3', 80, bits=10, meter=work)
        for N in range(1, 81):
            row = S.evaluate_A(source, N, work)
            direct = sum((N//d)*(int(source.prefix_w[d])-int(source.prefix_w[d-1]))
                         for d in range(1, N+1))
            up = sum(N//d for d in range(2, N+1) if int(source.mu[d]) == -1)
            down = sum(N//d for d in range(2, N+1) if int(source.mu[d]) == 1)
            work.charge(6*N)
            self.assertEqual(row['center_numerator'], direct)
            self.assertEqual(row['upward_uncertainty_count'], up)
            self.assertEqual(row['downward_uncertainty_count'], down)
            self.assertEqual(row['lower_numerator'], direct-down)
            self.assertEqual(row['upper_numerator'], direct+up)
            self.assertEqual(row['denominator'], 1 << 10)
            self.assertLessEqual(row['hyperbola_blocks'], 2*math.isqrt(N))
            self.assertIs(type(row['center_numerator']), int)
            self.assertFalse(row['float_admission_used'])

    def test_unrounded_arb_direct_sums_are_enclosed_with_both_error_signs(self):
        work = meter()
        source = S.make_source('1/3', 64, bits=16, meter=work)
        for N in (1, 2, 12, 37, 64):
            row = S.evaluate_A(source, N, work)
            lo, hi = direct_unrounded('1/3', N, work)
            self.assertLessEqual(Q(row['lower_numerator'], row['denominator']), lo)
            self.assertGreaterEqual(Q(row['upper_numerator'], row['denominator']), hi)
        row = S.evaluate_A(source, 6, work)
        self.assertGreater(row['upward_uncertainty_count'], 0)
        self.assertGreater(row['downward_uncertainty_count'], 0)

    def test_unit_and_generic_rational_exponents_no_root_whitelist(self):
        work = meter()
        for alpha in ('1/2', '1/3', '2/3', '1/4', '1/5', '1/257'):
            source = S.make_source(alpha, 16, bits=8, meter=work)
            unit = S.evaluate_A(source, 1, work)
            self.assertEqual(unit['lower_numerator'], 0)
            self.assertEqual(unit['upper_numerator'], 0)
            self.assertEqual(unit['downward_uncertainty_count'], 0)
            self.assertEqual(source.metadata()['alpha'], alpha)
            self.assertEqual(source.construction_counts['total_primitive_counts']['quantized_atoms'],
                             sum(int(source.mu[d]) != 0 for d in range(2, 17)))

    def test_declared_refinement_schedule_and_honest_unresolved_failure(self):
        work = meter()
        seen = []
        def injected(d, exponent, bits, precision, supplied_meter):
            seen.append(precision)
            supplied_meter.charge(16)
            return arb(3) if precision == 256 else arb(3, 1)
        with patch.object(S, '_atom_ball', injected):
            result = S._quantized_atom(2, Q(1, 2), 8, work)
        self.assertEqual(result, 3)
        self.assertEqual(seen, [128, 192, 256])
        self.assertEqual(work.atom_refinement_counts, {'128': 0, '192': 0, '256': 1})
        failed = meter()
        with patch.object(S, '_atom_ball', lambda *args: arb(3, 1)):
            with self.assertRaises(ArithmeticError):
                S._quantized_atom(2, Q(1, 2), 8, failed)
        self.assertEqual(sum(failed.atom_refinement_counts.values()), 0)

    def test_directed_floor_endpoints_use_attempt_precision_not_global53(self):
        work = meter()
        outer_precision = ctx.prec
        def injected(*args):
            return arb(3)-arb(1)/(1 << 80)
        with ctx.workprec(53), patch.object(S, '_atom_ball', injected):
            value = S._quantized_atom(2, Q(1, 2), 8, work)
        self.assertEqual(value, 2)
        self.assertEqual(work.atom_attempt_counts, {'128': 1, '192': 0, '256': 0})
        self.assertEqual(ctx.prec, outer_precision)

    def test_overflow_and_memory_preflight_without_large_arrays(self):
        work = meter()
        preflight = S.resource_preflight('1/2', 1_000_000, 36, work)
        self.assertLessEqual(preflight['prefix_abs_upper_integer'], (1 << 63)-1)
        self.assertEqual(preflight['persistent_array_bytes'], 25*1_000_001)
        self.assertTrue(preflight['overflow_preflight_proved'])
        with self.assertRaises(OverflowError):
            S.resource_preflight('1/2', 2_000_000, 40, work)
        with patch.object(S.np, 'ones', side_effect=AssertionError('allocation forbidden')):
            with self.assertRaises(OverflowError):
                S.make_source('1/2', 2_000_000, 40, work)
        with self.assertRaises(MemoryError):
            work.reserve(S.MAX_BUILD_BYTES+1)

    def test_canonical_parameters_query_and_deadline_guards(self):
        work = meter()
        for alpha in ('0', '1', '2/4', '-1/3', '+1/2', 0.5):
            with self.assertRaises(ValueError):
                S.make_source(alpha, 8, meter=work)
        for max_n in (0, True, S.MAX_N+1):
            with self.assertRaises(ValueError):
                S.make_source('1/2', max_n, meter=work)
        for bits in (0, True, 41):
            with self.assertRaises(ValueError):
                S.make_source('1/2', 8, bits, work)
        with self.assertRaises(OverflowError):
            S.make_source('1/'+str(1 << 4096), 8, meter=work)
        source = S.make_source('1/2', 8, meter=work)
        for N in (0, True, 9):
            with self.assertRaises(ValueError):
                S.evaluate_A(source, N, work)
        with self.assertRaises(OverflowError):
            S.make_source('1/2', 8, meter=meter(cap=0))
        expired = meter()
        expired.deadline = time.monotonic()-1
        with self.assertRaises(TimeoutError):
            S.make_source('1/2', 8, meter=expired)

    def test_extension_preserves_old_prefix_and_only_admits_new_atoms(self):
        work = meter()
        source = S.make_source('1/3', 20, bits=12, meter=work)
        seen = []
        original_atom = S._quantized_atom
        def tracked(d, *args, **kwargs):
            seen.append(d)
            self.assertGreater(d, 20)
            return original_atom(d, *args, **kwargs)
        extension_work = meter()
        with patch.object(S, '_quantized_atom', tracked):
            extended = S.extend_source(source, 61, extension_work)
        expected_indices = [d for d in range(21, 62) if int(extended.mu[d]) != 0]
        self.assertEqual(seen, expected_indices)
        for name in ('mu', 'prefix_w', 'prefix_up', 'prefix_down'):
            self.assertTrue(np.array_equal(getattr(source, name), getattr(extended, name)[:21]))
        scratch = S.make_source('1/3', 61, bits=12, meter=work)
        for name in ('mu', 'prefix_w', 'prefix_up', 'prefix_down'):
            self.assertTrue(np.array_equal(getattr(scratch, name), getattr(extended, name)))
        self.assertEqual(extended.reused_prefix_through, 20)
        self.assertEqual(extended.construction_counts['total_primitive_counts']['quantized_atoms'], len(expected_indices))
        self.assertEqual(sum(extended.atom_admission_counts.values()),
                         sum(int(extended.mu[d]) != 0 for d in range(2, 62)))
        self.assertGreaterEqual(extended.construction_counts['peak_bytes_estimate'],
                                extended.overflow_certificate['estimated_peak_bytes']+25*21)
        for N in (1, 12, 20, 37, 61):
            a = S.evaluate_A(extended, N, work)
            b = S.evaluate_A(scratch, N, work)
            self.assertEqual((a['lower_numerator'], a['upper_numerator']),
                             (b['lower_numerator'], b['upper_numerator']))

    def test_extension_mu_agreement_and_strict_domain_guards(self):
        work = meter()
        source = S.make_source('1/2', 8, bits=12, meter=work)
        for horizon in (7, 8, True, S.MAX_N+1):
            with self.assertRaises(ValueError):
                S.extend_source(source, horizon, work)
        bad_mu = source.mu.copy()
        bad_mu[2] = 1
        bad_mu.flags.writeable = False
        changed = replace(source, mu=bad_mu)
        with self.assertRaises(ArithmeticError):
            S.extend_source(changed, 12, work)

    def test_worker_transport_preserves_dtype_values_and_readonly_contract(self):
        work = meter()
        source = S.make_source('1/4', 12, bits=12, meter=work)
        transported = pickle.loads(pickle.dumps(source))
        work.charge(4*13)
        for name in ('mu', 'prefix_w', 'prefix_up', 'prefix_down'):
            array = getattr(transported, name)
            self.assertFalse(array.flags.writeable)
            self.assertEqual(array.dtype, getattr(source, name).dtype)
            self.assertTrue(np.array_equal(array, getattr(source, name)))
        self.assertEqual(S.evaluate_A(source, 12, work)['lower_numerator'],
                         S.evaluate_A(transported, 12, work)['lower_numerator'])


if __name__ == '__main__':
    path = Path(__file__).with_name('prime_scale_source_053_development.json')
    if path.exists():
        raise SystemExit('retain prior focused receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(SourceTests))
    counts = [v.counts() for v in METERS]
    receipt = {'schema': 'prime-scale-source-053-development-v1', 'invocations': [{
        'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'elapsed_seconds': time.monotonic()-started,
        'operations': sum(v['operations'] for v in counts)}],
        'atom_attempt_counts': {str(p): sum(v['atom_attempt_counts'][str(p)] for v in counts)
                                for p in S.PRECISION_SCHEDULE},
        'atom_refinement_counts': {str(p): sum(v['atom_refinement_counts'][str(p)] for v in counts)
                                   for p in S.PRECISION_SCHEDULE},
        'total_primitive_counts': {key: sum(v['total_primitive_counts'][key] for v in counts)
                                 for key in S.Meter().primitives},
        'peak_bytes_estimate': max((v['peak_bytes_estimate'] for v in counts), default=0),
        'scope': 'small synthetic sources/queries/extensions and allocation-free capacity preflight; no actual pilot arrays or values',
        'actual_pilot_applied': False, 'old_suites_or_studies_replayed': False,
        'independent_checker_imported': False, 'all_scale_bound_claimed': False}
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
