"""Synthetic signed floor/step fixtures and closed calibrations only."""
from fractions import Fraction as F
import json
from pathlib import Path
import time
import unittest

from flint import arb, ctx
import floor_residual_interval_043 as evaluator

METERS = []


def meter(**kwargs):
    value = evaluator.Meter(**kwargs)
    METERS.append(value)
    return value


def program(coefficients=(), steps=(), identifier='synthetic'):
    return {'id': identifier,
            'coefficients': [{'n': n, 'value': str(c)} for n, c in coefficients],
            'steps': [{'q': q, 'value': str(d)} for q, d in steps]}


def dyadic(pair):
    return F(int(pair[0]))*F(2)**pair[1]


def covers(bounds, value):
    return dyadic(bounds['lower_dyadic']) <= value <= dyadic(bounds['upper_dyadic'])


def residue(p, k):
    return 1-sum(F(row['value'])*(k % row['n'])/row['n'] for row in p['coefficients']) \
            -sum(F(row['value']) for row in p['steps'] if k >= row['q'])


def exact_head(p, H):
    return sum((residue(p, k)**2/F(k*(k+1)) for k in range(1, H+1)), F(0))


class FloorResidualIntervalTests(unittest.TestCase):
    def setUp(self):
        self.meter = meter()

    def test_basis_cells_and_indicator_endpoints(self):
        for n in (2, 3, 7):
            for k in range(1, 21):
                for x in (F(1, k), (F(1, k)+F(1, k+1))/2):
                    inverse = 1/x
                    scaled = 1/(n*x)
                    f = F(inverse.numerator//inverse.denominator, n)-scaled.numerator//scaled.denominator
                    self.assertEqual(f, F(k % n, n))
                    self.meter.charge(12)
                self.assertEqual(F(1, k) <= F(1, n), k >= n)

    def test_integer_lattice_signed_exact_residues(self):
        p = program([(2, F(3, 2)), (3, F(-2, 5)), (6, F(7, 3))],
                    [(2, F(1, 2)), (5, F(-3, 7))])
        lattice = evaluator.integer_lattice(p, self.meter)
        D, A, current = lattice['D'], lattice['A'], lattice['D']
        for k in range(1, 81):
            current += -A+sum(event for n, event in lattice['events'] if k % n == 0) \
                      +sum(event for q, event in lattice['step_events'] if q == k)
            self.assertEqual(F(current, D), residue(p, k))
            formula = D-k*A+sum(event*(k//n) for n, event in lattice['events']) \
                      +sum(event for q, event in lattice['step_events'] if q <= k)
            self.assertEqual(current, formula)
            self.meter.charge(24)
        for n, weight in lattice['weights']:
            c = next(F(row['value']) for row in p['coefficients'] if row['n'] == n)
            self.assertEqual(F(weight, D), c/n)

    def test_event_head_against_direct_rational_sums(self):
        fixtures = [program(), program([(2, F(2))]),
                    program([(2, F(3, 2)), (3, F(-2, 5)), (6, F(7, 3))],
                            [(2, F(1, 2)), (5, F(-3, 7))]),
                    program([(7, F(-1, 257)), (11, F(2, 3))], [(3, F(-1, 4))])]
        for p in fixtures:
            for H in (5, 17, 64):
                report = evaluator.certify(p, H, meter=self.meter)
                self.assertTrue(covers(report['head']['enclosure'], exact_head(p, H)))
                self.assertEqual(report['head']['indices'], [1, H])
                json.dumps(report)

    def test_constant_residual_whole_integral_calibration(self):
        for H in (0, 1, 17, 128):
            report = evaluator.certify(program(), H, meter=self.meter)
            self.assertTrue(covers(report['head']['enclosure'], F(H, H+1)))
            self.assertTrue(covers(report['norm_squared'], F(1)))
            self.assertEqual(report['tail']['upper'], str(F(1, H+1)))
            self.assertEqual(report['tail']['measure'], str(F(1, H+1)))

    def test_step_only_exact_zero_tail_calibration(self):
        p = program(steps=[(2, F(1, 2)), (3, F(1, 2))])
        report = evaluator.certify(p, 8, meter=self.meter)
        self.assertEqual(report['tail']['pointwise_abs_bound'], '0')
        self.assertEqual(report['tail']['upper'], '0')
        self.assertTrue(covers(report['norm_squared'], F(13, 24)))
        self.assertTrue(covers(report['head']['enclosure'], F(13, 24)))
        self.assertTrue(report['tail']['every_step_active_on_tail'])

    def test_closed_floor_norm_log_calibration(self):
        # With c2=2, e(k)=1 on even k and0 on odd k, so integral=1-log(2).
        report = evaluator.certify(program([(2, F(2))]), 128, meter=self.meter)
        with ctx.workprec(256):
            norm = 1-arb(2).log()
            bounds = report['norm_squared']
            lower = arb(int(bounds['lower_dyadic'][0]))*arb(2)**bounds['lower_dyadic'][1]
            upper = arb(int(bounds['upper_dyadic'][0]))*arb(2)**bounds['upper_dyadic'][1]
            self.assertTrue(lower < norm < upper)

    def test_tail_bound_uses_all_signed_steps_and_floor_magnitudes(self):
        p = program([(2, F(-3, 2)), (7, F(4, 3))],
                    [(2, F(-5, 4)), (5, F(3, 4))])
        report = evaluator.certify(p, 16, meter=self.meter)
        M = abs(1-F(-5, 4)-F(3, 4))+F(3, 2)*F(1, 2)+F(4, 3)*F(6, 7)
        self.assertEqual(F(report['tail']['pointwise_abs_bound']), M)
        self.assertEqual(F(report['tail']['upper']), M*M/17)
        for k in range(17, 200):
            self.assertLessEqual(abs(residue(p, k)), M)
            self.meter.charge(12)
        self.assertFalse(report['tail']['observations_used_to_infer_tail'])

    def test_steps_are_once_only_and_collide_with_periodic_events(self):
        p = program([(2, F(1)), (4, F(-1, 2))], [(4, F(3, 2))])
        report = evaluator.certify(p, 16, meter=self.meter)
        self.assertTrue(covers(report['head']['enclosure'], exact_head(p, 16)))
        D = int(report['lattice']['D'])
        self.assertEqual(report['lattice']['step_events'], [{'q': 4, 'value': str(-3*D//2)}])

    def test_whole_norm_scope_and_counts(self):
        report = evaluator.certify(program([(2, F(1, 257))]), 8, meter=self.meter)
        self.assertTrue(report['continuous_global_fixed_program_bound'])
        self.assertTrue(report['tail_is_analytic_global_bound'])
        for flag in ('float_sign_admission_used', 'convergence_as_support_increases_proved',
                     'actual_source_coefficient_recovery_claimed', 'RH_proved', 'RH_refuted'):
            self.assertFalse(report[flag])
        self.assertGreater(report['counts']['operations'], 0)
        self.assertGreater(report['counts']['peak_integer_bits'], 0)
        self.assertGreater(report['counts']['peak_bytes_estimate'], 0)
        self.assertEqual(report['support'], 1)

    def test_schema_order_zero_float_and_step_tail_rejections(self):
        for p in (program([(1, F(1))]), program([(2, F(1)), (2, F(2))]),
                  program([(3, F(1)), (2, F(1))]), program([(2, F(0))]),
                  program(steps=[(3, F(1)), (2, F(1))])):
            with self.assertRaises(ValueError):
                evaluator.certify(p, 8, meter=self.meter)
        p = program([(2, F(1))])
        p['coefficients'][0]['value'] = 0.5
        with self.assertRaises(ValueError):
            evaluator.certify(p, 8, meter=self.meter)
        p = program()
        del p['steps']
        with self.assertRaises(ValueError):
            evaluator.certify(p, 8, meter=self.meter)
        with self.assertRaises(ValueError):
            evaluator.certify(program(steps=[(9, F(1))]), 8, meter=self.meter)

    def test_resource_guards_before_event_allocation(self):
        with self.assertRaises(OverflowError):
            evaluator.certify(program([(2, F(1))]), 8, meter=meter(cap=0))
        for H in (True, -1, evaluator.MAX_H+1):
            with self.assertRaises(ValueError):
                evaluator.certify(program(), H, meter=self.meter)
        with self.assertRaises(ValueError):
            evaluator.certify(program(), 8, precision=53, meter=self.meter)
        with self.assertRaises(ValueError):
            evaluator.certify(program([(n, F(1)) for n in range(2, 259)]), 8, meter=self.meter)
        with self.assertRaises(OverflowError):
            self.meter.product(1 << 8191, 2)


if __name__ == '__main__':
    started = time.monotonic()
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(FloorResidualIntervalTests)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    invocation = {'returncode': 0 if result.wasSuccessful() else 1,
                  'tests': result.testsRun, 'failures': len(result.failures), 'errors': len(result.errors),
                  'elapsed_seconds': time.monotonic()-started,
                  'operations': sum(m.operations for m in METERS),
                  'peak_integer_bits': max(m.peak_integer_bits for m in METERS),
                  'peak_bytes_estimate': max(m.peak_bytes_estimate for m in METERS),
                  'exposure': 'synthetic rational floor/step fixtures and closed calibrations only'}
    path = Path(__file__).with_name('floor_residual_interval_043_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else {
        'schema': 'floor-residual-interval-development-v1', 'invocations': [],
        'actual_new_programs_evaluated': False, 'parent_source_data_read': False,
        'old_suites_or_studies_rerun': False, 'hashes_generated': False}
    receipt['invocations'].append(invocation)
    receipt['cumulative_operations'] = sum(run['operations'] for run in receipt['invocations'])
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    raise SystemExit(invocation['returncode'])
