"""Source-free common-atom fixtures for the Boolean insertion backend."""
from copy import deepcopy
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import pickle
import time
import unittest
from unittest.mock import patch
import numpy as np
import prime_insertion_source_055 as S

METERS = []


def meter(**kwargs):
    value = S.Meter(**kwargs)
    METERS.append(value)
    return value


def mu(n):
    if n == 0:
        return 0
    rest, count = n, 0
    for p in range(2, math.isqrt(n)+1):
        if rest % p == 0:
            rest //= p
            count += 1
            if rest % p == 0:
                return 0
    return (-1)**(count+(rest > 1))


def atom(d):
    return 0 if d == 1 else 1+d % 7


def fixture(X=151, bits=10):
    """Common arbitrary integer atom function, not logarithm observations."""
    center = np.zeros(X+1, dtype=np.int64)
    down = np.zeros(X+1, dtype=np.int64)
    up = np.zeros(X+1, dtype=np.int64)
    for n in range(2, X+1):
        divisors = [d for d in range(2, n+1) if n % d == 0]
        center[n] = -sum(mu(d)*atom(d) for d in divisors)
        down[n] = sum(mu(d) == 1 for d in divisors)
        up[n] = sum(mu(d) == -1 for d in divisors)
    arrays = dict(zip(('Acenter', 'Adown', 'Aup'),
                      [np.cumsum(a, dtype=np.int64) for a in (center, down, up)]))
    ell = X.bit_length()
    metadata = {'schema': 'prime-scale-dense-source-v1', 'alpha': '1/5',
                'max_n': X, 'dyadic_bits': bits,
                'arrays': {name: {'dtype': 'int64', 'domain': [0, X], 'writeable': False}
                           for name in arrays},
                'overflow_certificate': {'max_n': X, 'bits': bits, 'ell': ell,
                    'center_abs_upper_integer': X*ell*(1+ell)*(1 << bits),
                    'uncertainty_upper_integer': X*(1+ell),
                    'int64_max': S.INT64_MAX, 'overflow_preflight_proved': True},
                'synthetic_injected_common_atoms': True}
    return {'alpha': '1/5', 'max_n': X, 'bits': bits, **arrays, 'metadata': metadata}


def local(array, n):
    return int(array[n])-int(array[n-1])


class InsertionTests(unittest.TestCase):
    def test_all_prefix_entries_shifted_identity_and_errors(self):
        fields = fixture()
        work = meter()
        bank = S.build_insertion_sources(fields, [(), (2,), (3,), (5,), (2, 3), (2, 5), (3, 5)], work)
        for primes, source in bank.sources.items():
            R = math.prod(primes)
            total_center = total_down = total_up = 0
            for n in range(2, source.max_n+1):
                coprime = math.gcd(n, R) == 1
                expected = (-sum(mu(d)*atom(R*d) for d in range(1, n+1) if n % d == 0)
                            if coprime else 0)
                subset = sum(sign*local(fields['Acenter'], n*divisor)
                             for _, _, divisor, sign in S._subsets(primes))
                self.assertEqual(subset, expected)
                self.assertEqual(local(source.Bcenter, n), expected)
                total_center += expected
                total_down += (local(fields['Adown'], n)+(R > 1)) if coprime else 0
                total_up += local(fields['Aup'], n) if coprime else 0
                self.assertEqual(int(source.Bcenter[n]), total_center)
                self.assertEqual(int(source.Bdown[n]), total_down)
                self.assertEqual(int(source.Bup[n]), total_up)
                work.charge(10*(n+1))
            for array in (source.Bcenter, source.Bdown, source.Bup):
                self.assertEqual(int(array[0]), 0)
                self.assertEqual(int(array[1]), 0)
        self.assertEqual(bank.metadata()['new_atoms_evaluated'], 0)

    def test_prime_powers_radical_invariance_and_unit_exclusion(self):
        fields = fixture()
        work = meter()
        bank = S.build_insertion_sources(fields, [(2,), (3,)], work)
        for p, n in ((2, 4), (2, 8), (3, 9), (3, 12)):
            self.assertEqual(local(fields['Acenter'], n), local(fields['Acenter'], p*n))
            self.assertEqual(local(bank.sources[(p,)].Bcenter, n), 0)
        for p in (2, 3):
            raw_unit = local(fields['Acenter'], 1)-local(fields['Acenter'], p)
            self.assertEqual(raw_unit, -atom(p))
            self.assertNotEqual(raw_unit, 0)
            self.assertEqual(int(bank.sources[(p,)].Bcenter[1]), 0)
        work.charge(80)

    def test_correlated_uncertainty_improves_subset_bound(self):
        fields = fixture()
        work = meter()
        bank = S.build_insertion_sources(fields, [(2, 3)], work)
        source = bank.sources[(2, 3)]
        improvements = 0
        for n in range(2, source.max_n+1):
            naive_down = naive_up = 0
            for _, _, d, sign in S._subsets((2, 3)):
                down, up = local(fields['Adown'], n*d), local(fields['Aup'], n*d)
                naive_down += down if sign > 0 else up
                naive_up += up if sign > 0 else down
            tight_down, tight_up = local(source.Bdown, n), local(source.Bup, n)
            self.assertLessEqual(tight_down, naive_down)
            self.assertLessEqual(tight_up, naive_up)
            improvements += tight_down+ tight_up < naive_down+naive_up
            work.charge(40)
        self.assertGreater(improvements, 0)

    def test_empty_identity_cache_and_readonly_transport(self):
        fields = fixture(X=101)
        work = meter()
        bank = S.build_insertion_sources(fields, [(), (2,), (2,), ()], work)
        self.assertEqual(len(bank.sources), 2)
        self.assertEqual(bank.construction_counts['total_primitive_counts']['source_cache_hits'], 2)
        for name in ('center', 'down', 'up'):
            self.assertIs(getattr(bank.sources[()], 'B'+name), fields['A'+name])
        transported = pickle.loads(pickle.dumps(bank))
        for primes in bank.sources:
            for name in ('Bcenter', 'Bdown', 'Bup'):
                self.assertTrue(np.array_equal(getattr(bank.sources[primes], name),
                                               getattr(transported.sources[primes], name)))
                self.assertFalse(getattr(transported.sources[primes], name).flags.writeable)
        work.charge(6*102)

    def test_boolean_polynomials_and_normal_forms(self):
        work = meter()
        self.assertEqual(S.normal_form([5, 2, 3, 2, 5], work), (2, 3, 5))
        for primes in ((), (2,), (3, 5), (2, 3, 5, 7)):
            cert = S.boolean_certificate('1/257', primes, work)
            self.assertEqual(cert['subset_terms'], cert['square_reduction'])
            self.assertEqual([r['atom_coefficient'] for r in cert['atom_cancellation_rows']],
                             [0]*((1 << len(primes))-1)+[1])
            self.assertFalse(cert['source_chain_replayed_here'])
            self.assertFalse(cert['all_scale_bound_proved'])
            self.assertEqual(cert['new_atoms_evaluated'], 0)
        for primes in ([2, 2], [3, 2], [4], [True]):
            with self.assertRaises(ValueError):
                S.boolean_certificate('1/5', primes, work)
        with self.assertRaises(ValueError):
            S.boolean_certificate('2/10', (), work)
        with self.assertRaises(ValueError):
            S.boolean_certificate('1', (), work)

    def test_signed_filter_exact_normalization(self):
        work = meter()
        bank = S.build_insertion_sources(fixture(), [(), (2,), (2, 3)], work)
        for primes in bank.sources:
            source = bank.sources[primes]
            for coeffs in ([2, -3, 1], [-1], [0, -2, 3]):
                value = S.evaluate_filter(bank, primes, 2, coeffs, 2, work)
                lower = upper = center = 0
                for j, c in enumerate(coeffs):
                    n = 2*(2**j)
                    mid = int(source.Bcenter[n])
                    lo = mid-int(source.Bdown[n])
                    hi = mid+int(source.Bup[n])
                    lower += c*(lo if c >= 0 else hi)
                    upper += c*(hi if c >= 0 else lo)
                    center += c*mid
                    self.assertEqual(value['term_rows'][j]['lower_numerator'], lo)
                    self.assertEqual(value['term_rows'][j]['upper_numerator'], hi)
                self.assertEqual(value['lower'], str(Q(5*lower, 1 << source.bits)))
                self.assertEqual(value['upper'], str(Q(5*upper, 1 << source.bits)))
                self.assertEqual(value['center_numerator'], center)
                self.assertLessEqual(Q(value['lower']), Q(value['upper']))
                self.assertEqual(value['source_support_used'], source.product*2**(len(coeffs)-1)*2)
                self.assertFalse(value['float_admission_used'])
                self.assertFalse(value['source_chain_replayed_here'])

    def test_metadata_binary_dimensions_and_source_consistency(self):
        work = meter()
        mutations = []
        bad = fixture(); bad['metadata']['arrays'] = []; mutations.append(bad)
        bad = fixture(); bad['metadata']['overflow_certificate']['ell'] += 1; mutations.append(bad)
        bad = fixture(); bad['Aup'] = bad['Aup'].astype(np.int32); mutations.append(bad)
        bad = fixture(); bad['Acenter'] = bad['Acenter'][:-1]; mutations.append(bad)
        bad = fixture(); bad['Adown'][1] = 1; mutations.append(bad)
        bad = fixture(); bad['Aup'][4] = bad['Aup'][3]-1; mutations.append(bad)
        bad = fixture(); bad['Acenter'][8] += 1; mutations.append(bad)
        bad = fixture(); bad['unexpected'] = 0; mutations.append(bad)
        for bad in mutations:
            with self.assertRaises(ValueError):
                S.build_insertion_sources(bad, [(2,)], work)
        with self.assertRaises(ValueError):
            S.build_insertion_sources(None, [()], work)
        with self.assertRaises(ValueError):
            S.build_insertion_sources(fixture(X=4), [(2, 3)], work)

    def test_resource_guards_before_native_accumulation(self):
        work = meter()
        bad = fixture(X=8)
        bad['max_n'], bad['bits'] = S.MAX_N, S.MAX_BITS
        with patch.object(S.np, 'subtract', side_effect=AssertionError('native arithmetic before guard')):
            with self.assertRaises(OverflowError):
                S.build_insertion_sources(bad, [()], work)
        bad = fixture(X=1000, bits=40)
        bound = bad['metadata']['overflow_certificate']['center_abs_upper_integer']
        bad['Acenter'][2::2] = bound
        bad['Acenter'][3::2] = -bound
        with patch.object(S.np, 'cumsum', side_effect=AssertionError('prefix before guard')):
            with self.assertRaises(OverflowError):
                S.build_insertion_sources(bad, [(2,)], work)
        with self.assertRaises(MemoryError):
            work.reserve(S.MAX_BYTES+1)

    def test_filter_domains_and_operational_caps(self):
        work = meter()
        bank = S.build_insertion_sources(fixture(X=31), [(), (2,)], work)
        for Sset, q, c, n in (([2, 2], 2, [1], 2), ([3], 2, [1], 2),
                             ([], 4, [1], 2), ([], 2, [1, 0], 2),
                             ([], 2, [True], 2), ([], 2, [65], 2),
                             ([], 2, [1], 1), ([2], 2, [1, -1], 8)):
            with self.assertRaises(ValueError):
                S.evaluate_filter(bank, Sset, q, c, n, work)
        with self.assertRaises(OverflowError):
            S.build_insertion_sources(fixture(X=8), [()], meter(cap=0))
        expired = meter()
        expired.deadline = time.monotonic()-1
        with self.assertRaises(TimeoutError):
            S.boolean_certificate('1/5', (), expired)


if __name__ == '__main__':
    path = Path(__file__).with_name('prime_insertion_source_055_development.json')
    if path.exists():
        raise SystemExit('retain prior focused receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(InsertionTests))
    counts = [m.counts() for m in METERS]
    receipt = {'schema': 'prime-insertion-source-055-development-v1', 'invocations': [{
        'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'elapsed_seconds': time.monotonic()-started,
        'operations': sum(c['operations'] for c in counts)}],
        'total_primitive_counts': {k: sum(c['total_primitive_counts'][k] for c in counts)
                                 for k in S.Meter().primitives},
        'peak_bytes_estimate': max((c['peak_bytes_estimate'] for c in counts), default=0),
        'scope': 'source-free common integer atom and prefix fixtures only; no archived arrays, mu source or logarithm atoms evaluated',
        'actual_pilot_applied': False, 'old_source_atoms_rerun': False,
        'old_suites_or_studies_replayed': False, 'checker_imported': False,
        'all_scale_bound_claimed': False}
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
