"""Source-free integer fixtures; no saved scientific prefix or atom is read."""
from copy import deepcopy
import json
import math
from pathlib import Path
import pickle
import time
import unittest
from unittest.mock import patch
import numpy as np

import prime_scale_dense_054 as S

METERS = []


def meter(**kwargs):
    result = S.Meter(**kwargs)
    METERS.append(result)
    return result


def toy_mu(n):
    if n == 0:
        return 0
    remaining, count = n, 0
    for p in range(2, math.isqrt(n)+1):
        if remaining % p == 0:
            remaining //= p
            count += 1
            if remaining % p == 0:
                return 0
    return (-1)**(count+(remaining > 1))


def fixture(X=101, bits=10, zero_atoms=False):
    """Inject bounded integer atomfloors, not actual logarithmic observations."""
    mu = np.asarray([toy_mu(n) for n in range(X+1)], dtype=np.int8)
    weights = np.zeros(X+1, dtype=np.int64)
    if not zero_atoms:
        for d in range(2, X+1):
            weights[d] = -int(mu[d])*(1+d % 7)
    up = np.asarray(mu == -1, dtype=np.int64)
    down = np.asarray(mu == 1, dtype=np.int64)
    down[1] = 0
    prefixes = {name: np.cumsum(array, dtype=np.int64) for name, array in
                (('prefix_w', weights), ('prefix_up', up), ('prefix_down', down))}
    ell = X.bit_length()
    metadata = {'schema': 'prime-scale-fractional-source-v1', 'alpha': '1/2',
                'max_n': X, 'dyadic_bits': bits,
                'arrays': {'mu': {'dtype': 'int8', 'domain': [0, X], 'writeable': False},
                           **{name: {'dtype': 'int64', 'domain': [0, X],
                                     'writeable': False, 'prefix_includes_index': True}
                              for name in prefixes}},
                'overflow_certificate': {'max_n': X, 'bits': bits, 'int64_max': S.INT64_MAX,
                    'log_power_upper_integer': ell, 'atom_abs_upper_integer': ell*(1 << bits),
                    'prefix_abs_upper_integer': (X-1)*ell*(1 << bits),
                    'uncertainty_prefix_upper_integer': X-1, 'overflow_preflight_proved': True},
                'atom_refinement_counts': {'128': int(np.count_nonzero(mu[2:])), '192': 0, '256': 0},
                'synthetic_injected_atoms': True}
    return {'alpha': '1/2', 'max_n': X, 'bits': bits, 'mu': mu,
            **prefixes, 'metadata': metadata}


def selected(coefficients=(1,), q=2, minimum=2, name='synthetic_word'):
    return {'id': name, 'request': {'alpha': '1/2', 'q': q,
                'coefficients': list(coefficients), 'bound': {'C': '2', 'log_power': '0',
                     'minimum': minimum, 'normalization': 'divide_by_alpha'}}}


def scalar_fixture(value, down=0, up=0):
    arrays = [np.zeros(5, dtype=np.int64) for _ in range(3)]
    for array, item in zip(arrays, (value, down, up)):
        array[4] = item
    return S.DenseSource('1/2', 4, 4, *arrays, {}, {})


class DenseTests(unittest.TestCase):
    def test_101_dense_entries_equal_direct_floor_sums(self):
        fields = fixture()
        work = meter()
        dense = S.dense_source(fields, work)
        w = [int(fields['prefix_w'][d])-int(fields['prefix_w'][d-1]) if d else 0
             for d in range(102)]
        for N in range(102):
            center = sum(w[d]*(N//d) for d in range(1, N+1))
            up = sum(N//d for d in range(2, N+1) if int(fields['mu'][d]) == -1)
            down = sum(N//d for d in range(2, N+1) if int(fields['mu'][d]) == 1)
            self.assertEqual(int(dense.Acenter[N]), center)
            self.assertEqual(int(dense.Aup[N]), up)
            self.assertEqual(int(dense.Adown[N]), down)
            work.charge(6*N)
        for array in (dense.Acenter, dense.Adown, dense.Aup):
            self.assertEqual(array.dtype, np.int64)
            self.assertFalse(array.flags.writeable)
        self.assertFalse(dense.metadata()['source_chain_replayed_here'])
        self.assertEqual(dense.metadata()['new_atoms_evaluated'], 0)
        self.assertEqual(dense.metadata()['persistent_array_bytes'], 24*102)

    def test_signed_filter_interval_retains_negative_coefficients(self):
        work = meter()
        dense = S.dense_source(fixture(), work)
        req = selected((2, -3, 1))['request']
        center, lo, hi, rows = S._filter_interval(req, dense, 12, work, include_rows=True)
        self.assertEqual(center, 2*int(dense.Acenter[12])-3*int(dense.Acenter[24])+int(dense.Acenter[48]))
        expected_lo = 2*(int(dense.Acenter[12])-int(dense.Adown[12]))
        expected_lo -= 3*(int(dense.Acenter[24])+int(dense.Aup[24]))
        expected_lo += int(dense.Acenter[48])-int(dense.Adown[48])
        expected_hi = 2*(int(dense.Acenter[12])+int(dense.Aup[12]))
        expected_hi -= 3*(int(dense.Acenter[24])-int(dense.Adown[24]))
        expected_hi += int(dense.Acenter[48])+int(dense.Aup[48])
        self.assertEqual((lo, hi), (expected_lo, expected_hi))
        self.assertEqual([r['scale'] for r in rows], [12, 24, 48])
        self.assertEqual(rows[1]['lower_numerator'], int(dense.Acenter[24])-int(dense.Adown[24]))

    def test_full_coverage_passes_skips_and_unseen_counts(self):
        work = meter()
        dense = S.dense_source(fixture(), work)
        row = S.first_counterexample(selected(), dense, [2, 3, 5, 11, 200], work)
        self.assertEqual(row['status'], 'FINITE_ALL_NEW_SCALES_PASS')
        self.assertEqual(row['new_scales_total'], 96)
        self.assertEqual(row['new_scales_tested'], 96)
        self.assertEqual(row['finite_pass_count'], 96)
        self.assertEqual(row['skip_scales_in_domain'], [2, 3, 5, 11])
        self.assertEqual(row['untested_after_counterexample'], 0)
        self.assertIsNone(row['first_counterexample'])
        self.assertFalse(row['all_scale'])

    def test_first_strict_counterexample_and_negative_sign(self):
        work = meter()
        dense = S.dense_source(fixture(bits=4), work)
        for sign in (1, -1):
            row = S.first_counterexample(selected((64*sign,)), dense, [], work)
            witness = row['first_counterexample']
            self.assertEqual(row['status'], 'FINITE_COUNTEREXAMPLE')
            self.assertEqual(witness['N'], 2)
            self.assertEqual(row['new_scales_tested'], 1)
            self.assertEqual(row['untested_after_counterexample'], 99)
            self.assertGreater(witness['comparison']['left'], witness['comparison']['right'])
            self.assertEqual(witness['comparison']['left'], witness['lower_abs_numerator']**2*4)
            self.assertEqual(witness['comparison']['right'], 4*2*(1 << 8))
            self.assertEqual(witness['Tcenter'], 64*sign*int(dense.Acenter[2]))
            self.assertFalse(witness['source_chain_replayed_here'])
            self.assertFalse(witness['float_or_root_comparison_used'])
        skipped = S.first_counterexample(selected((64,)), dense, [2, 3], work)
        self.assertGreater(skipped['first_counterexample']['N'], 3)
        self.assertEqual(skipped['skip_scales_in_domain'], [2, 3])

    def test_exact_equality_passes_and_zero_straddling_stays_unresolved(self):
        work = meter()
        for value in (32, -32):
            row = S.first_counterexample(selected(minimum=4), scalar_fixture(value), [], work)
            self.assertEqual(row['finite_pass_count'], 1)
            self.assertIsNone(row['first_counterexample'])
        strict = S.first_counterexample(selected(minimum=4), scalar_fixture(-33), [], work)
        self.assertEqual(strict['first_counterexample']['lower_abs_numerator'], 33)
        unresolved = S.first_counterexample(selected(minimum=4), scalar_fixture(0, 64, 64), [], work)
        self.assertEqual(unresolved['status'], 'NO_COUNTEREXAMPLE_WITH_UNRESOLVED')
        self.assertEqual(unresolved['unresolved_count'], 1)
        self.assertIsNone(unresolved['first_counterexample'])

    def test_python_integer_filter_avoids_int64_combination_overflow(self):
        work = meter()
        row = S.first_counterexample(selected((2,), minimum=4), scalar_fixture(1 << 62), [], work)
        witness = row['first_counterexample']
        self.assertEqual(witness['Tcenter'], 1 << 63)
        self.assertIs(type(witness['Tcenter']), int)
        self.assertGreater(witness['comparison']['left'], 1 << 126)

    def test_dense_overflow_guard_precedes_arrays_and_tracks_absolute_signs(self):
        work = meter()
        guard = S.resource_preflight(128000, 32, work)
        self.assertLess(guard['center_abs_upper_integer'], 1 << 63)
        bad = {'alpha': '1/2', 'max_n': 2_000_000, 'bits': 40, 'mu': None,
               'prefix_w': None, 'prefix_up': None, 'prefix_down': None, 'metadata': {}}
        with patch.object(S.np, 'empty', side_effect=AssertionError('allocation forbidden')):
            with self.assertRaises(OverflowError):
                S.dense_source(bad, work)
        with self.assertRaises(MemoryError):
            work.reserve(S.MAX_BYTES+1)

    def test_prefix_metadata_binary_and_sign_validation(self):
        work = meter()
        bads = []
        wrong_dtype = fixture()
        wrong_dtype['prefix_w'] = wrong_dtype['prefix_w'].astype(np.int32)
        bads.append(wrong_dtype)
        wrong_domain = fixture()
        wrong_domain['mu'] = wrong_domain['mu'][:-1]
        bads.append(wrong_domain)
        wrong_metadata = fixture()
        wrong_metadata['metadata']['max_n'] = 100
        bads.append(wrong_metadata)
        binary = fixture()
        binary['prefix_up'][2:] += 1
        bads.append(binary)
        signed = fixture()
        signed['prefix_w'][2] = -1
        bads.append(signed)
        unit = fixture()
        unit['prefix_down'][1] = 1
        bads.append(unit)
        bad_refinements = fixture()
        bad_refinements['metadata']['atom_refinement_counts']['128'] += 1
        bads.append(bad_refinements)
        overflowed = fixture()
        overflowed['prefix_w'][2] = -(1 << 63)
        bads.append(overflowed)
        for fields in bads:
            with self.assertRaises(ValueError):
                S.dense_source(fields, work)

    def test_selected_typed_scope_and_empty_domain(self):
        work = meter()
        dense = S.dense_source(fixture(X=16), work)
        bads = []
        for key, value in (('alpha', '2/4'), ('q', 4), ('coefficients', [1, 0]),
                           ('coefficients', [True]), ('coefficients', [65])):
            entry = selected()
            entry['request'][key] = value
            bads.append(entry)
        for key, value in (('C', '3'), ('log_power', '1/2'), ('normalization', 'none')):
            entry = selected()
            entry['request']['bound'][key] = value
            bads.append(entry)
        extra = selected()
        extra['extra'] = True
        bads.append(extra)
        for entry in bads:
            with self.assertRaises(ValueError):
                S.first_counterexample(entry, dense, [], work)
        empty = S.first_counterexample(selected((1, -1, 1, -1), q=5), dense, [], work)
        self.assertEqual(empty['status'], 'NO_NEW_SCALES')
        self.assertEqual(empty['new_scales_total'], 0)
        with self.assertRaises(ValueError):
            S.first_counterexample(selected(), dense, [True], work)

    def test_operational_caps_and_worker_transport(self):
        with self.assertRaises(OverflowError):
            S.dense_source(fixture(X=8), meter(cap=0))
        expired = meter()
        expired.deadline = time.monotonic()-1
        with self.assertRaises(TimeoutError):
            S.dense_source(fixture(X=8), expired)
        work = meter()
        dense = S.dense_source(fixture(X=12), work)
        copy = pickle.loads(pickle.dumps(dense))
        for name in ('Acenter', 'Adown', 'Aup'):
            self.assertTrue(np.array_equal(getattr(dense, name), getattr(copy, name)))
            self.assertFalse(getattr(copy, name).flags.writeable)
        work.charge(3*13)


if __name__ == '__main__':
    path = Path(__file__).with_name('prime_scale_dense_054_development.json')
    if path.exists():
        raise SystemExit('retain prior focused receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(DenseTests))
    counts = [m.counts() for m in METERS]
    receipt = {'schema': 'prime-scale-dense-054-development-v1', 'invocations': [{
        'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'elapsed_seconds': time.monotonic()-started,
        'operations': sum(c['operations'] for c in counts)}],
        'total_primitive_counts': {key: sum(c['total_primitive_counts'][key] for c in counts)
                                 for key in S.Meter().primitives},
        'peak_bytes_estimate': max((c['peak_bytes_estimate'] for c in counts), default=0),
        'scope': 'source-free injected integer atom/prefix/scalar fixtures only; no saved source array or logarithm evaluated',
        'actual_pilot_applied': False, 'old_source_atoms_rerun': False,
        'old_suites_or_studies_replayed': False, 'checker_imported': False,
        'all_scale_bound_claimed': False}
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
