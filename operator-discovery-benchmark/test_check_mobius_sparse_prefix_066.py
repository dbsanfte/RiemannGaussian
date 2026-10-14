"""Synthetic-only 066 tests; fixture construction uses pointwise differences.

No producer imports, frozen files, saved studies, or numerical LPs are read.
"""
import copy
import itertools
import json
import resource
import time
import unittest
from fractions import Fraction as Q
from unittest import mock
import check_mobius_sparse_prefix_066 as C


class ChargeOnly:
    def __init__(self):
        self.operations = 0

    def charge(self, n=1):
        self.operations += n


METER = ChargeOnly()


def trial_mu(n):
    sign, divisor = 1, 2
    while divisor*divisor <= n:
        if n % divisor == 0:
            n //= divisor
            sign = -sign
            if n % divisor == 0:
                return 0
        divisor += 1
    return -sign if n > 1 else sign


def source(N, y, p, q, ratio, d):
    if d > y:
        return Q(0)
    def W(base):
        return 4*N//(base*d)-3*(2*N//(base*d))+2*(N//(base*d))
    return Q(W(p))-ratio*W(q)


def fixture(N=12, y=3, H=12, p=2, q=3, tau=True):
    D = 4*N//p
    H = min(H, D)
    parameters = dict(primes=[p, q], p=p, q=q, alpha='1/2', gamma='1/3')
    if tau:
        parameters['tau'] = '1/4'
    cert = dict(schema=C.SCHEMA, parameters=parameters, N=N, y=y, H=H, endpoints=[])
    for ratio in (Q(p, q), Q(1)):
        floors = {}
        for base, scale in ((p, Q(1)), (q, -ratio)):
            for v, a in ((4, 1), (2, -3), (1, 2)):
                Z = v*N//base
                if Z:
                    floors[Z] = floors.get(Z, Q(0))+scale*a
        floors = {Z: a for Z, a in floors.items() if a}
        # Derive the step representation from pointwise correction jumps,
        # instead of enumerating the producer/checker's tail index i.
        correction = [Q(0)]*(D+2)
        for d in range(1, D+1):
            correction[d] = source(N, y, p, q, ratio, d)-sum(
                (a*(Z//d) for Z, a in floors.items()), Q(0))
        steps = {T: correction[T]-correction[T+1] for T in range(1, D+1)
                 if correction[T] != correction[T+1]}
        rows = []
        for j in range(1, H+1):
            weights = [sum((a for T, a in steps.items()
                            if T//(j+1) < n <= T//j), Q(0)) for n in range(1, D+1)]
            segments = []
            n = 1
            while n <= D:
                if not weights[n-1]:
                    n += 1
                    continue
                lo, a = n, weights[n-1]
                while n < D and weights[n] == a:
                    n += 1
                segments.append(dict(lo=lo, hi=n, coefficient=str(a)))
                n += 1
            direct = floors.get(j, Q(0))
            coefficient = sum((trial_mu(n)*(source(N, y, p, q, ratio, j*n)-
                                 source(N, y, p, q, ratio, (j+1)*n))
                               for n in range(1, D+1)), Q(0))
            assert coefficient == direct+sum((trial_mu(n)*a for n, a in enumerate(weights, 1)), Q(0))
            cost = abs(direct)+sum(map(abs, weights), Q(0))
            rows.append(dict(j=j, direct=str(direct), segments=segments,
                             coefficient=str(coefficient), interval_l1=str(cost)))
        tails = []
        for J in range(1, H+1):
            joined = sum((Q(row['interval_l1']) for row in rows[J-1:]), Q(0))
            actual = sum((abs(Q(row['coefficient'])) for row in rows[J-1:]), Q(0))
            coarse = sum((abs(a) for Z, a in floors.items() if J <= Z <= H), Q(0))+sum(
                (abs(a)*(T//J-T//(H+1)) for T, a in steps.items()), Q(0))
            tails.append(dict(J=J, H=H, joined_interval_upper=str(joined),
                              coarse_upper=str(coarse), actual_variation=str(actual)))
        cert['endpoints'].append(dict(ratio=str(ratio),
            floors=[dict(horizon=Z, coefficient=str(a)) for Z, a in sorted(floors.items())],
            steps=[dict(horizon=T, coefficient=str(a)) for T, a in sorted(steps.items())],
            rows=rows, step_first_moment=str(sum((abs(a)*T for T, a in steps.items()), Q(0))),
            floor_l1=str(sum(map(abs, floors.values()), Q(0))),
            coefficient_l1=str(sum((abs(Q(row['coefficient'])) for row in rows), Q(0))), tail_bounds=tails))
    return cert


def accept(cert):
    return C.verify_sparse(cert, METER)


class Tests(unittest.TestCase):
    def reject(self, cert):
        with self.assertRaises((ValueError, OverflowError, MemoryError)):
            accept(cert)

    def test_scope_is_actual_raw_and_open_full_target(self):
        out = accept(fixture())
        for flag in ('verified', 'source_rewrite_proved', 'actual_mobius_inverse_identity_proved',
                     'raw_short_only', 'uniform_tail_rule_reviewed', 'ordinary_mu_unit_retained',
                     'squareful_mu_zero_retained', 'independent_parent_063_admission_required'):
            self.assertIs(out[flag], True)
        for flag in ('RH_proved', 'uniform_full_variation_proved', 'uniform_N_growth_proved',
                     'whole_signed_target_bound_proved', 'original_source_binding_proved',
                     'original_sqrt_radius_preserved', 'scientific_source_or_LP_evaluated'):
            self.assertIs(out[flag], False)
        self.assertEqual(out['arithmetic_query_horizon'], 24)

    def test_tiny_unit_y1_and_every_boundary(self):
        for y in (1, 2, 3, 4):
            for H in range(1, 5):
                accept(fixture(N=2, y=y, H=H))

    def test_y_at_and_below_H_with_floor_horizons_inside_H(self):
        for y in (2, 3, 7, 8, 9):
            accept(fixture(N=8, y=y, H=16))

    def test_untruncated_prefix_contracts_to_floor_deltas(self):
        cert = fixture(N=12, y=24, H=24)
        out = accept(cert)
        for endpoint in cert['endpoints']:
            self.assertEqual(endpoint['steps'], [])
            self.assertTrue(all(row['coefficient'] == row['direct'] for row in endpoint['rows']))
        self.assertTrue(all(e['step_first_moment'] == '0' for e in out['endpoints']))

    def test_signed_two_channel_coalescing(self):
        cert = fixture(N=18, y=4, H=20)
        accept(cert)
        for endpoint in cert['endpoints']:
            values = [Q(a['coefficient']) for a in endpoint['steps']]
            self.assertTrue(any(a < 0 for a in values))
            self.assertTrue(any(a > 0 for a in values))
            self.assertGreater(Q(endpoint['step_first_moment']),
                abs(sum((Q(a['coefficient'])*a['horizon'] for a in endpoint['steps']), Q(0))))

    def test_optional_tau_and_distinct_prime_pairs(self):
        for p, q in ((2, 3), (3, 5), (5, 7)):
            accept(fixture(N=15, y=2, H=9, p=p, q=q, tau=False))

    def test_full_floor_forward_source_reconstruction(self):
        for N, y in itertools.product(range(2, 10), (1, 2, 3)):
            cert = fixture(N=N, y=y, H=2*N)
            accept(cert)
            for endpoint in cert['endpoints']:
                for d in range(1, 2*N+1):
                    rebuilt = sum((Q(row['coefficient'])*(row['j']//d)
                                   for row in endpoint['rows']), Q(0))
                    self.assertEqual(rebuilt, source(N, y, 2, 3, Q(endpoint['ratio']), d))

    def test_exhaustive_small_prefix_rows_and_all_tails(self):
        for N in range(2, 13):
            for y in range(1, 2*N+1):
                cert = fixture(N=N, y=y, H=min(7, 2*N))
                out = accept(cert)
                for endpoint in out['endpoints']:
                    for tail in endpoint['tail_bounds']:
                        self.assertLessEqual(Q(tail['actual_variation']), Q(tail['joined_interval_upper']))
                        self.assertLessEqual(Q(tail['joined_interval_upper']), Q(tail['coarse_upper']))
                        self.assertLessEqual(Q(tail['coarse_upper']),
                            Q(endpoint['floor_l1'])+Q(endpoint['step_first_moment'])/tail['J'])

    def test_ordinary_mu_unit_prime_and_squareful_values(self):
        context = C._Context(ChargeOnly())
        mu, mertens = C._ordinary_mu(64, context)
        self.assertEqual(mu, [0]+[trial_mu(n) for n in range(1, 65)])
        self.assertEqual(mu[1], 1)
        self.assertEqual([mu[n] for n in (2, 3, 5)], [-1, -1, -1])
        self.assertEqual([mu[n] for n in (4, 8, 9, 12, 16, 18, 25)], [0]*7)
        self.assertEqual(mertens[64], sum(mu))
        accept(fixture(N=32, y=30, H=32))

    def test_mu_unit_omission_is_rejected(self):
        cert = fixture(N=2, y=1, H=4)
        row = cert['endpoints'][0]['rows'][0]
        unit_weight = sum((Q(a['coefficient']) for a in row['segments'] if a['lo'] == 1), Q(0))
        self.assertNotEqual(unit_weight, 0)
        row['coefficient'] = str(Q(row['coefficient'])-unit_weight)
        self.reject(cert)

    def test_prime_sign_substitution_for_squareful_mu_is_rejected(self):
        cert = fixture(N=32, y=7, H=16)
        for row in cert['endpoints'][0]['rows']:
            extra = sum((Q(a['coefficient']) for a in row['segments'] if a['lo'] <= 4 <= a['hi']), Q(0))
            if extra:
                row['coefficient'] = str(Q(row['coefficient'])+extra)
                self.reject(cert)
                break
        else:
            self.fail('fixture must expose squareful n=4')

    def test_every_coefficient_and_cost_tamper(self):
        baseline = fixture()
        for endpoint in range(2):
            for row_index in range(baseline['H']):
                for field in ('direct', 'coefficient', 'interval_l1'):
                    cert = copy.deepcopy(baseline)
                    row = cert['endpoints'][endpoint]['rows'][row_index]
                    row[field] = str(Q(row[field])+1)
                    self.reject(cert)

    def test_every_tail_field_tamper(self):
        baseline = fixture()
        for tail_index in range(baseline['H']):
            for field in ('joined_interval_upper', 'coarse_upper', 'actual_variation'):
                cert = copy.deepcopy(baseline)
                tail = cert['endpoints'][0]['tail_bounds'][tail_index]
                tail[field] = str(Q(tail[field])+1)
                self.reject(cert)

    def test_aggregate_tamper(self):
        for field in ('floor_l1', 'step_first_moment', 'coefficient_l1'):
            cert = fixture()
            cert['endpoints'][0][field] = str(Q(cert['endpoints'][0][field])+1)
            self.reject(cert)

    def test_missing_floor_step_and_zero_atoms(self):
        for field in ('floors', 'steps'):
            cert = fixture()
            cert['endpoints'][0][field].pop()
            self.reject(cert)
            cert = fixture()
            cert['endpoints'][0][field][0]['coefficient'] = '0'
            self.reject(cert)

    def test_atom_horizon_and_signed_coefficient_tamper(self):
        for field in ('floors', 'steps'):
            cert = fixture()
            cert['endpoints'][0][field][0]['horizon'] += 1
            self.reject(cert)
            cert = fixture()
            atom = cert['endpoints'][0][field][0]
            atom['coefficient'] = str(-Q(atom['coefficient']))
            self.reject(cert)

    def test_duplicate_and_unsorted_atoms(self):
        for field in ('floors', 'steps'):
            cert = fixture()
            cert['endpoints'][0][field].reverse()
            self.reject(cert)
            cert = fixture()
            cert['endpoints'][0][field].insert(0, copy.deepcopy(cert['endpoints'][0][field][0]))
            self.reject(cert)

    def test_missing_head_middle_last_row(self):
        for index in (0, 3, -1):
            cert = fixture()
            cert['endpoints'][0]['rows'].pop(index)
            self.reject(cert)

    def test_missing_tail_head_middle_last(self):
        for index in (0, 3, -1):
            cert = fixture()
            cert['endpoints'][0]['tail_bounds'].pop(index)
            self.reject(cert)

    def test_tail_index_and_terminal_horizon(self):
        for field in ('J', 'H'):
            cert = fixture()
            cert['endpoints'][0]['tail_bounds'][3][field] -= 1
            self.reject(cert)

    def test_segment_omission_endpoint_coefficient(self):
        for field in ('lo', 'hi', 'coefficient'):
            cert = fixture()
            segment = cert['endpoints'][0]['rows'][0]['segments'][0]
            segment[field] = str(Q(segment[field])+1) if field == 'coefficient' else segment[field]+1
            self.reject(cert)
        cert = fixture()
        cert['endpoints'][0]['rows'][0]['segments'].pop()
        self.reject(cert)

    def test_nonmaximal_adjacent_segments_rejected(self):
        cert = fixture(N=32, y=3, H=8)
        segments = cert['endpoints'][0]['rows'][0]['segments']
        for index, segment in enumerate(segments):
            if segment['hi'] > segment['lo']:
                second = copy.deepcopy(segment)
                second['lo'] += 1
                segment['hi'] = segment['lo']
                segments.insert(index+1, second)
                self.reject(cert)
                break
        else:
            self.fail('fixture must expose splittable segment')

    def test_endpoint_missing_swapped_ratio_and_fake_ratio(self):
        cert = fixture(); cert['endpoints'].pop(); self.reject(cert)
        cert = fixture(); cert['endpoints'].reverse(); self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['ratio'] = '3/4'; self.reject(cert)

    def test_no_repair_free_sign_or_unknown_fields(self):
        for field in ('repair', 'core_inverse', 'conditioned_primes', 'prime_signs', 'budget'):
            cert = fixture(); cert[field] = []; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['terms'] = []; self.reject(cert)
        cert = fixture(); cert['schema'] = 'mobius-walsh-energy-bound-v1'; self.reject(cert)

    def test_parameter_gates(self):
        for field, value in (('p', 3), ('q', 2), ('alpha', '0'), ('alpha', '1'),
                             ('gamma', '0'), ('tau', '1'), ('primes', [2, 4]),
                             ('primes', [3, 2]), ('primes', [2, 2, 3])):
            cert = fixture(); cert['parameters'][field] = value; self.reject(cert)

    def test_strict_integer_and_capacity_gates(self):
        for field, value in (('N', True), ('N', 1), ('N', 65537), ('y', False),
                             ('y', 0), ('y', 25), ('H', True), ('H', 0), ('H', 25)):
            cert = fixture(); cert[field] = value; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['j'] = True; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['steps'][0]['horizon'] = True; self.reject(cert)
        cert = fixture(); cert['endpoints'][0]['rows'][0]['segments'][0]['lo'] = True; self.reject(cert)

    def test_noncanonical_and_overbit_rational_gates(self):
        for value in ('2/2', '0.5', ' 1', '1/0', '', str(1 << 4096)):
            cert = fixture(); cert['endpoints'][0]['ratio'] = value; self.reject(cert)

    def test_intermediate_bit_work_and_storage_guards(self):
        c = C._Context(ChargeOnly())
        with self.assertRaises(OverflowError):
            c.mul(Q(1 << 3000), Q(1 << 3000))
        with self.assertRaises(OverflowError):
            C.verify_sparse(fixture(), C.Meter(cap=0))
        with mock.patch.object(C, 'MAX_WORK', 20):
            with self.assertRaises(OverflowError):
                C.verify_sparse(fixture(), ChargeOnly())
        with mock.patch.object(C, 'MAX_MEMORY_BYTES', 9000):
            with self.assertRaises(MemoryError):
                C.verify_sparse(fixture(), ChargeOnly())
        with mock.patch.object(C, 'MAX_ENTRIES', 3):
            with self.assertRaises(OverflowError):
                C.verify_sparse(fixture(), ChargeOnly())


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(Tests)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    report = dict(schema='mobius-sparse-prefix-checker-development-v1',
                  synthetic_only=True, tests_run=result.testsRun, failures=len(result.failures),
                  errors=len(result.errors), successful=result.wasSuccessful(),
                  charged_work_units=METER.operations, wall_seconds=time.monotonic()-started,
                  peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    print(json.dumps(report, sort_keys=True))
    raise SystemExit(0 if result.wasSuccessful() else 1)
