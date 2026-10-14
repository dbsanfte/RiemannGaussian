"""Tiny synthetic arithmetic/calibration tests; no pilot source values."""
from fractions import Fraction as Q
import json
import math
from pathlib import Path
import time
import unittest
from unittest.mock import patch
from flint import arb, ctx
import prime_insertion_middle_source_057 as S

METERS = []


def meter(**kwargs):
    result = S.Meter(**kwargs)
    METERS.append(result)
    return result


def request(N=3, primes=(2,), alpha='1/2', gamma='1', lo='0', hi='1'):
    return {'alpha': alpha, 'primes': list(primes), 'N': N, 'gamma': gamma,
            'lower_fraction': lo, 'upper_fraction': hi}


def radical_primes(n):
    rest, factors = n, []
    for p in range(2, math.isqrt(n)+1):
        if rest % p == 0:
            factors.append(p)
            while rest % p == 0:
                rest //= p
    if rest > 1:
        factors.append(rest)
    return factors


def direct_coefficients(N, primes):
    out = {}
    for n in range(2, 4*N+1):
        c = 2*(n <= N)-3*(n <= 2*N)+(n <= 4*N)
        terms = [(1, 1)]
        for p in radical_primes(n*math.prod(primes)):
            terms += [(d*p, -sign) for d, sign in terms]
        for base, sign in terms:
            out[base] = out.get(base, 0)+c*sign
    return tuple(sorted((base, weight) for base, weight in out.items() if weight))


def exact_arb(q):
    return arb(q.numerator)/q.denominator


class MiddleTests(unittest.TestCase):
    def test_cofactor_source_equals_all_radical_columns(self):
        work = meter()
        context = S.prepare_context(work)
        for N in (2, 3, 5, 7):
            for primes in ((), (2,), (3,), (2, 3), (3, 5)):
                actual = S._compile(primes, N, context, work)
                self.assertEqual(actual, direct_coefficients(N, primes))
                self.assertEqual(sum(w for _, w in actual), 0)
                self.assertTrue(all(base > 1 for base, _ in actual))
                work.charge(4*N*100)

    def test_insertion_keeps_shared_primes_and_p_squared(self):
        work = meter()
        context = S.prepare_context(work)
        for primes, N in (((2,), 4), ((3,), 3), ((2, 3), 5)):
            rows = S._compile(primes, N, context, work)
            with patch.object(S, '_compile', return_value=rows):
                value = S.evaluate(request(N, primes), meter=work, context=context)
            self.assertEqual(rows, direct_coefficients(N, primes))
            self.assertTrue(value['source']['all_valuations_retained'])
            self.assertIn('no coprime mask on n', value['source']['source_kind'])
            self.assertTrue(value['source']['unit_cancelled_exactly'])

    def test_half_alpha_erfc_calibration_admits_high_precision(self):
        work = meter()
        context = S.prepare_context(work)
        req = request(3, (2, 3))
        proposal = S.evaluate(req, precision=128, meter=work, context=context)
        old = ctx.prec
        try:
            ctx.prec = 256
            a, b = arb(1)/3, arb(1)/2
            total = arb(0)
            for base, c in direct_coefficients(3, (2, 3)):
                lam = arb(base).log()
                def endpoint(t):
                    return 2*(-lam*t).exp()/t.sqrt()-2*(arb.pi()*lam).sqrt()*(lam*t).sqrt().erfc()
                total += c*(endpoint(a)-endpoint(b))
            total /= arb.pi().sqrt()
            self.assertTrue(exact_arb(Q(proposal['lower'])) <= total.lower())
            self.assertTrue(total.upper() <= exact_arb(Q(proposal['upper'])))
            work.charge(200*len(direct_coefficients(3, (2, 3))))
        finally:
            ctx.prec = old

    def test_normalization_and_fractional_exponent_precision(self):
        work = meter()
        context = S.prepare_context(work)
        for alpha in ('1/3', '1/257', '256/257'):
            req = request(3, (3,), alpha=alpha, gamma='257/128', lo='1/3', hi='2/3')
            low = S.evaluate(req, precision=128, meter=work, context=context)
            high = S.evaluate(req, precision=256, meter=work, context=context)
            self.assertLessEqual(Q(low['lower']), Q(high['upper']))
            self.assertLessEqual(Q(high['lower']), Q(low['upper']))
            self.assertEqual(high['source']['normalization'], '1/Gamma(1-alpha)')
            self.assertEqual(high['output_dyadic_bits'], 80)
            for field in (high, *high['endpoint_intervals'].values()):
                for key in ('lower', 'upper'):
                    self.assertEqual(Q(field[key]).denominator & (Q(field[key]).denominator-1), 0)
                    self.assertLessEqual(Q(field[key]).denominator, 1 << 80)

    def test_exact_zero_bands_no_arithmetic_or_special_functions(self):
        work = meter()
        context = S.prepare_context(work)
        with patch.object(S, '_compile', side_effect=AssertionError('source in zero band')):
            with patch.object(S, '_atom', side_effect=AssertionError('gamma in zero band')):
                for req in (request(2, gamma='1'), request(4, gamma='1/2'),
                            request(3, gamma='1/257'), request(3, lo='1/3', hi='1/3')):
                    value = S.evaluate(req, meter=work, context=context)
                    self.assertEqual(value['lower'], '0')
                    self.assertEqual(value['upper'], '0')
                    self.assertEqual(value['status'], 'EXACT_ZERO_BAND')
                    self.assertEqual(value['counts']['total_primitive_counts']['gamma_upper_atoms'], 0)
                    self.assertIsNone(value['source']['coefficient_count'])
                    self.assertFalse(value['source_chain_replayed_here'])

    def test_cache_functional_keys_and_precision_restoration(self):
        work = meter()
        context = S.prepare_context(work)
        old = ctx.prec
        req = request(4, (2,))
        first = S.evaluate(req, precision=192, meter=work, context=context)
        second = S.evaluate(req, precision=192, meter=work, context=context)
        self.assertEqual((first['lower'], first['upper']), (second['lower'], second['upper']))
        self.assertEqual(second['counts']['total_primitive_counts']['gamma_upper_atoms'], 0)
        self.assertEqual(second['counts']['total_primitive_counts']['mu_sieve_entries'], 0)
        changed = S.evaluate(request(4, (2,), gamma='2'), precision=192, meter=work, context=context)
        self.assertEqual(changed['counts']['total_primitive_counts']['gamma_upper_atoms'],
                         changed['source']['coefficient_count'])
        self.assertEqual(changed['counts']['total_primitive_counts']['power_atoms'], 0)
        self.assertEqual(ctx.prec, old)
        with patch.object(S, '_atom', side_effect=ArithmeticError('synthetic fail')):
            with self.assertRaises(ArithmeticError):
                S.evaluate(request(4, (2,), gamma='3'), precision=256, meter=work, context=context)
        self.assertEqual(ctx.prec, old)

    def test_partition_signed_additivity(self):
        work = meter()
        context = S.prepare_context(work)
        req = request(3, (2,))
        partition = S.band_decomposition(req, ('0', '1/3', '1/2', '2/3', '1'), work)
        whole = S.evaluate(partition['whole_request'], meter=work, context=context)
        bands = [S.evaluate(r, meter=work, context=context) for r in partition['band_requests']]
        self.assertLessEqual(sum(Q(v['lower']) for v in bands), Q(whole['upper']))
        self.assertGreaterEqual(sum(Q(v['upper']) for v in bands), Q(whole['lower']))
        self.assertFalse(partition['numeric_values_evaluated'])
        self.assertFalse(partition['head_or_tail_bounded'])
        with self.assertRaises(ValueError):
            S.band_decomposition(req, ('0', '1/3', '1/3', '1'), work)

    def test_exact_signed_grid_rounding_and_bounded_formatter(self):
        work = meter()
        old = ctx.prec
        try:
            ctx.prec = 192
            for q in (Q(0), Q(1, 3), Q(-1, 3), Q(1, 2**200), Q(-1, 2**200)):
                output = S._interval(exact_arb(q), work)
                self.assertLessEqual(Q(output['lower']), q)
                self.assertGreaterEqual(Q(output['upper']), q)
            self.assertEqual(S._interval(arb(0), work), {'lower': '0', 'upper': '0'})
            integer = 1 << 15000
            text = S._integer_text(integer)
            # Verify long decimal output without changing the native parse guard.
            restored = 0
            for start in range(0, len(text), 9):
                chunk = text[start:start+9]
                restored = restored*10**len(chunk)+int(chunk)
            self.assertEqual(restored, integer)
            self.assertGreater(len(text), 4300)
            work.charge(len(text))
        finally:
            ctx.prec = old

    def test_adversarial_request_and_cost_guards(self):
        work = meter()
        mutations = []
        for key, value in (('alpha', '1'), ('alpha', '2/4'), ('gamma', '0'),
                           ('N', True), ('N', S.MAX_N+1), ('primes', [4]),
                           ('primes', [2, 2]), ('primes', [3, 2]),
                           ('lower_fraction', '-1'), ('upper_fraction', '2')):
            bad = request(); bad[key] = value; mutations.append(bad)
        bad = request(lo='2/3', hi='1/3'); mutations.append(bad)
        bad = request(); bad['extra'] = 0; mutations.append(bad)
        for bad in mutations:
            with self.assertRaises(ValueError):
                S.evaluate(bad, meter=work)
        with self.assertRaises(ValueError):
            S.evaluate(request(), precision=129, meter=work)
        with self.assertRaises(OverflowError):
            S.evaluate(request(gamma='1/'+str(1 << 1000)), meter=work)
        with self.assertRaises(OverflowError):
            S.evaluate(request(), meter=meter(cap=0))
        expired = meter(); expired.deadline = time.monotonic()-1
        with self.assertRaises(TimeoutError):
            S.evaluate(request(), meter=expired)
        with self.assertRaises(MemoryError):
            work.reserve(S.MAX_WORKING_BYTES+1)
        context = S.prepare_context(work, max_bytes=0)
        result = S.evaluate(request(), meter=work, context=context)
        self.assertEqual(context.bytes_estimate, 0)
        self.assertFalse(result['all_scale'])
        self.assertFalse(result['whole_source_bound_proved'])
        self.assertFalse(result['head_or_tail_evaluated'])


if __name__ == '__main__':
    path = Path(__file__).with_name('prime_insertion_middle_source_057_development.json')
    if path.exists():
        raise SystemExit('retain prior focused receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(MiddleTests))
    counts = [m.counts() for m in METERS]
    receipt = {'schema': 'prime-insertion-middle-source-057-development-v1', 'invocations': [{
        'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'elapsed_seconds': time.monotonic()-started,
        'operations': sum(v['operations'] for v in counts)}],
        'total_primitive_counts': {k: sum(v['total_primitive_counts'][k] for v in counts)
                                 for k in S.Meter().primitives},
        'peak_bytes_estimate': max((v['peak_bytes_estimate'] for v in counts), default=0),
        'scope': 'tiny synthetic N<=7 arithmetic and special-function calibrations only; no pilot data or old study',
        'actual_pilot_applied': False, 'old_suites_or_studies_replayed': False,
        'checker_imported': False, 'all_scale_bound_claimed': False}
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
