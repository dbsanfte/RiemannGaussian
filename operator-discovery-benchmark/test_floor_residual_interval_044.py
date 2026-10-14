"""Synthetic general signed vectors; no actual frozen recipe/norm observation."""
from fractions import Fraction as F
import json
import math
from pathlib import Path
import time
import unittest

import floor_residual_interval_044 as evaluator

METERS = []


def meter(**kwargs):
    instance = evaluator.Meter(**kwargs)
    METERS.append(instance)
    return instance


def program(constant=F(1), floors=(), steps=()):
    return {'id': 'synthetic', 'constant': str(constant),
            'coefficients': [{'n': n, 'value': str(c)} for n, c in floors],
            'steps': [{'q': q, 'value': str(d)} for q, d in steps]}


def value(p, k, active_steps=False):
    return F(p['constant'])-sum(F(row['value'])*F(k % row['n'], row['n']) for row in p['coefficients']) \
           -sum(F(row['value']) for row in p['steps'] if active_steps or k >= row['q'])


def dyadic(pair):
    return F(int(pair[0]))*F(2)**pair[1]


def covers(bounds, exact):
    return dyadic(bounds['lower_dyadic']) <= exact <= dyadic(bounds['upper_dyadic'])


class SignedVectorTests(unittest.TestCase):
    def setUp(self):
        self.meter = meter()

    def test_general_integer_updates_and_direct_rational_head(self):
        fixtures = [program(F(0), [(2, F(3, 2)), (3, F(-1, 7))], [(2, F(-3, 4))]),
                    program(F(-2, 257), [(4, F(-5, 3)), (6, F(7, 5))], [(5, F(1, 2))]),
                    program(F(3, 7)), program(F(0))]
        for p in fixtures:
            lattice = evaluator.integer_lattice(p, self.meter)
            R = lattice['CD']
            for k in range(1, 41):
                R += -lattice['A']+sum(event for n, event in lattice['periodic'] if k % n == 0) \
                     +sum(event for q, event in lattice['one_time'] if k == q)
                self.assertEqual(F(R, lattice['D']), value(p, k))
                self.meter.charge(16)
            for H in (8, 31):
                report = evaluator.certify(p, H, meter=self.meter)
                exact = sum((value(p, k)**2/F(k*(k+1)) for k in range(1, H+1)), F(0))
                self.assertTrue(covers(report['head']['enclosure'], exact))
                json.dumps(report)

    def test_periodic_energy_against_full_small_period(self):
        p = program(F(-1, 3), [(2, F(3, 2)), (3, F(-4, 7)), (4, F(5, 3))], [(2, F(-2, 5))])
        lattice = evaluator.integer_lattice(p, self.meter)
        energy = evaluator.periodic_energy(lattice, self.meter)
        period = math.lcm(*(row['n'] for row in p['coefficients']))
        samples = [value(p, k, True) for k in range(period)]
        mean, V = sum(samples)/period, sum(x*x for x in samples)/period
        self.assertEqual(energy['mean'], mean)
        self.assertEqual(energy['V'], V)
        self.assertEqual(energy['variance'], V-mean*mean)

    def test_jordan_identity_and_signed_gcd_replay(self):
        p = program(F(0), [(2, F(1)), (3, F(-2)), (4, F(-2)), (6, F(3)), (8, F(-1, 2))])
        lattice = evaluator.integer_lattice(p, self.meter)
        energy = evaluator.periodic_energy(lattice, self.meter)
        weights = dict(lattice['weights'])
        ordered = sum(wm*wn*(math.gcd(m, n)**2-1) for m, wm in weights.items() for n, wn in weights.items())
        jordan = sum(int(row['J2'])*int(row['weighted_sum'])**2 for row in energy['jordan_divisor_sums'])
        self.assertEqual(jordan, ordered)
        self.assertEqual(jordan, energy['integer_variance_numerator'])
        self.assertEqual(energy['pair_count'], len(weights)**2)
        cache = evaluator.JordanKernel()
        J = cache.get(32, self.meter)
        for m in range(2, 17):
            for n in range(2, 17):
                self.assertEqual(sum(J[d] for d in range(2, min(m, n)+1) if m % d == n % d == 0),
                                 math.gcd(m, n)**2-1)
                self.meter.charge(12)

    def test_zero_signed_divisor_sum_is_retained(self):
        p = program(F(0), [(2, F(1)), (4, F(-2))])
        report = evaluator.certify(p, 16, meter=self.meter)
        rows = report['periodic_energy']['jordan_divisor_sums']
        self.assertEqual([r['d'] for r in rows], [2, 4])
        self.assertEqual(rows[0]['weighted_sum'], '0')
        self.assertTrue(report['periodic_energy']['all_signed_pairs_retained'])

    def test_covariance_rational_kernel_calibration(self):
        kernel = evaluator.GCDKernel()
        for m, n in ((2, 3), (2, 4), (3, 6), (4, 4)):
            P = math.lcm(m, n)
            xm, xn = F(m-1, 2*m), F(n-1, 2*n)
            direct = sum((F(k % m, m)-xm)*(F(k % n, n)-xn) for k in range(P))/P
            self.assertEqual(kernel.rational(m, n, self.meter), direct)
            self.assertEqual(kernel.rational(n, m, self.meter), direct)
        self.assertGreater(kernel.hits, 0)

    def test_primary_safe_large_sieve_finite_blocks(self):
        p = program(F(0), [(2, F(1)), (3, F(-3, 2)), (5, F(2, 3))], [(2, F(1, 4))])
        report = evaluator.certify(p, 32, meter=self.meter)
        V, K = F(report['periodic_energy']['V']), report['periodic_energy']['K']
        for start in (2, 7, 19):
            for length in (1, 4, 17, 51):
                block = sum(value(p, k, True)**2 for k in range(start, start+length))
                self.assertLessEqual(block, (length+K*K)*V)
                self.meter.charge(16*length)
        theorem = report['imported_large_sieve']
        self.assertEqual(theorem['block_bound'], '(L+K^2)*V')
        self.assertFalse(theorem['minus_one_sharpening_used'])
        self.assertFalse(theorem['detector_discovered_theorem'])

    def test_weighted_tail_factor_and_complete_upper(self):
        p = program(F(0), [(2, F(1)), (3, F(-1)), (4, F(1, 2))], [(2, F(1, 3))])
        H = 32
        report = evaluator.certify(p, H, meter=self.meter)
        a, K = H+1, report['periodic_energy']['K']
        V = F(report['periodic_energy']['V'])
        factor = F(1, a)+F(K*K, a*(a+1))
        self.assertEqual(F(report['imported_large_sieve']['weighted_tail_factor']), factor)
        self.assertEqual(F(report['tail']['large_sieve_upper']), V*factor)
        self.assertEqual(F(report['tail']['upper']), min(F(report['tail']['pointwise_upper']), V*factor))
        observed_partial = sum(value(p, k)**2/F(k*(k+1)) for k in range(a, 257))
        self.assertLessEqual(observed_partial, F(report['tail']['upper']))
        self.assertFalse(report['tail']['observations_used_to_infer_tail'])

    def test_constant_zero_and_step_only_exact_norms(self):
        zero = evaluator.certify(program(F(0)), 0, meter=self.meter)
        self.assertEqual(zero['tail']['upper'], '0')
        self.assertTrue(covers(zero['norm_squared'], F(0)))
        constant = evaluator.certify(program(F(-2, 7)), 16, meter=self.meter)
        self.assertTrue(covers(constant['norm_squared'], F(4, 49)))
        step = evaluator.certify(program(F(0), steps=[(2, F(1))]), 16, meter=self.meter)
        self.assertTrue(covers(step['norm_squared'], F(1, 2)))
        compact = evaluator.certify(program(F(1), steps=[(2, F(1))]), 16, meter=self.meter)
        self.assertEqual(compact['tail']['upper'], '0')
        self.assertTrue(covers(compact['norm_squared'], F(1, 2)))

    def test_jordan_cache_reused_across_signed_vectors(self):
        cache = evaluator.JordanKernel()
        evaluator.certify(program(F(0), [(3, F(1)), (7, F(2))]), 8, meter=self.meter, kernel=cache)
        evaluator.certify(program(F(1), [(2, F(-1)), (5, F(2))]), 8, meter=self.meter, kernel=cache)
        self.assertEqual(cache.maximum, 7)
        self.assertGreater(cache.hits, 0)
        self.assertEqual(len(cache.values), 8)

    def test_expanded_support_and_scope(self):
        p = program(F(0), [(n, F(1 if n % 2 else -1, 257)) for n in range(2, 259)])
        report = evaluator.certify(p, 8, meter=self.meter)
        self.assertEqual(report['support'], 257)
        self.assertEqual(report['periodic_energy']['pair_count'], 257**2)
        self.assertTrue(report['continuous_global_fixed_vector_bound'])
        self.assertTrue(report['target_role_requires_constant1_and_no_steps'])
        for flag in ('general_vector_is_automatically_RH_bearing', 'convergence_as_support_increases_proved',
                     'source_coefficient_recovery_claimed', 'actual_source_data_read', 'RH_proved', 'RH_refuted',
                     'float_norm_or_sign_admission_used'):
            self.assertFalse(report[flag])

    def test_schema_domain_and_resource_rejections(self):
        for p in (program(F(1), [(2, F(0))]), program(F(1), [(3, F(1)), (2, F(1))]),
                  program(F(1), [(4097, F(1))])):
            with self.assertRaises(ValueError):
                evaluator.certify(p, 8, meter=self.meter)
        p = program()
        p['constant'] = 0.5
        with self.assertRaises(ValueError):
            evaluator.certify(p, 8, meter=self.meter)
        with self.assertRaises(ValueError):
            evaluator.certify(program(steps=[(9, F(1))]), 8, meter=self.meter)
        with self.assertRaises(OverflowError):
            evaluator.certify(program(), 8, meter=meter(cap=0))
        for H in (True, -1, evaluator.MAX_H+1):
            with self.assertRaises(ValueError):
                evaluator.certify(program(), H, meter=self.meter)
        with self.assertRaises(ValueError):
            evaluator.certify(program(), 8, precision=53, meter=self.meter)


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(SignedVectorTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    invocation = {'returncode': 0 if result.wasSuccessful() else 1,
                  'tests': result.testsRun, 'failures': len(result.failures), 'errors': len(result.errors),
                  'elapsed_seconds': time.monotonic()-started,
                  'operations': sum(m.operations for m in METERS),
                  'peak_integer_bits': max(m.peak_integer_bits for m in METERS),
                  'peak_bytes_estimate': max(m.peak_bytes_estimate for m in METERS),
                  'exposure': 'synthetic signed vectors, exact covariance/Jordan checks and analytic-tail calibrations only'}
    path = Path(__file__).with_name('floor_residual_interval_044_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else {
        'schema': 'floor-signed-vector-norm-development-v1', 'invocations': [],
        'actual_new_programs_observed': False, 'actual_source_data_read': False,
        'frozen_files_modified': False, 'old_suites_or_studies_rerun': False, 'hashes_generated': False}
    receipt['invocations'].append(invocation)
    receipt['cumulative_operations'] = sum(row['operations'] for row in receipt['invocations'])
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(invocation['returncode'])
