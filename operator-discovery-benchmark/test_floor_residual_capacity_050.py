"""Focused synthetic capacity tests; no scientific source or old suite replay."""
from fractions import Fraction as F
import json
from pathlib import Path
import sys
import time
import unittest

import floor_residual_capacity_050 as C
import floor_residual_capacity_045 as OLD_CAPACITY
import floor_residual_interval_044 as OLD_INTERVAL
import check_floor_residual_arguments_044 as OLD_CHECK

WORK = []


def vector(name, rows, constant='1', steps=()):
    return {'id': name, 'constant': constant,
            'coefficients': [{'n': n, 'value': str(v)} for n, v in rows],
            'steps': [{'q': q, 'value': str(v)} for q, v in steps]}


def replay(program, H):
    meter = C.INTERVAL.Meter()
    proof = C.CHECK.Meter()
    try:
        cert = C.INTERVAL.certify(program, H=H, precision=192, meter=meter,
                                   kernel=C.INTERVAL.JordanKernel())
        checked = C.CHECK.verify_norm(program, cert, meter=proof)
        return cert, checked
    finally:
        WORK.extend([meter.operations, proof.operations])


class CapacityTests(unittest.TestCase):
    def test_isolation_and_unchanged_input_horizon_limits(self):
        for backend in (OLD_INTERVAL, OLD_CHECK):
            self.assertEqual(backend.MAX_INDEX, 4096)
            self.assertEqual(backend.MAX_SUPPORT, 2048)
        for backend in (OLD_CAPACITY.INTERVAL, OLD_CAPACITY.CHECK):
            self.assertEqual(backend.MAX_INDEX, 4096)
            self.assertEqual(backend.MAX_SUPPORT, 3072)
        self.assertEqual(OLD_INTERVAL.MAX_INTEGER_BITS, 8192)
        self.assertEqual(OLD_CHECK.MAX_RESULT_BITS, 8192)
        self.assertEqual(C.INTERVAL.MAX_INTEGER_BITS, 16384)
        self.assertEqual(C.CHECK.MAX_RESULT_BITS, 16384)
        self.assertEqual(C.INTERVAL.MAX_PARAMETER_BITS, 4096)
        self.assertEqual(C.CHECK.MAX_BITS, 4096)
        self.assertEqual(C.INTERVAL.MAX_H, OLD_INTERVAL.MAX_H)
        huge = vector('oversize_input', [(2, 1 << 4096)])
        for validate in (C.INTERVAL.validate_program, C.CHECK.verify_program):
            with self.assertRaises(ValueError):
                validate(huge)

    def test_large_indices_step_and_exact_head(self):
        program = vector('large_index_rational_toy', [(4098, F(3, 7)),
                           (4995, F(-5, 11))], constant='-2/3',
                         steps=[(4099, F(-1, 5))])
        cert, checked = replay(program, 4100)
        self.assertTrue(checked['verified'])
        self.assertEqual(checked['independent_precision'], 256)
        self.assertFalse(checked['convergence_proved'])
        direct = sum((F(-2, 3) - F(3, 7)*F(k % 4098, 4098)
                       + F(5, 11)*F(k % 4995, 4995)
                       + (F(1, 5) if k >= 4099 else 0))**2 / (k*(k+1))
                     for k in range(1, 4101))
        endpoints = C.CHECK.Meter()
        low = C.CHECK._dyadic(cert['head']['enclosure']['lower_dyadic'], endpoints)
        high = C.CHECK._dyadic(cert['head']['enclosure']['upper_dyadic'], endpoints)
        WORK.append(endpoints.operations)
        self.assertLessEqual(low, direct)
        self.assertGreaterEqual(high, direct)
        self.assertEqual(cert['periodic_energy']['K'], 4995)
        for validate in (OLD_INTERVAL.validate_program, OLD_CAPACITY.CHECK.verify_program):
            with self.assertRaises(ValueError):
                validate(program)

    def test_new_support_limit_is_real_and_bounded(self):
        program = vector('4096_signed_floor_toy', [(n, (-1 if n % 2 else 1)*n)
                                                   for n in range(2, 4098)])
        cert, checked = replay(program, 4)
        self.assertEqual(cert['support'], 4096)
        self.assertTrue(checked['all_domain_included'])
        with self.assertRaises(ValueError):
            OLD_CAPACITY.INTERVAL.validate_program(program)
        too_many = vector('4097_toy', [(n, n) for n in range(2, 4099)])
        too_far = vector('5001_toy', [(5001, 1)])
        for validate in (C.INTERVAL.validate_program, C.CHECK.verify_program):
            for bad in (too_many, too_far):
                with self.assertRaises(ValueError):
                    validate(bad)

    def test_lattice_square_really_crosses_old8192_bit_guard(self):
        program = vector('large_lattice_toy', [(2, F(1, 2**2300)),
                                               (3, F(-1, 3**1400))], constant='0')
        cert, checked = replay(program, 0)
        self.assertTrue(checked['verified'])
        self.assertGreater(cert['counts']['peak_integer_bits'], 8192)
        self.assertLessEqual(cert['counts']['peak_integer_bits'], 16384)
        old_meter = OLD_INTERVAL.Meter()
        try:
            with self.assertRaises(OverflowError):
                OLD_INTERVAL.certify(program, H=0, precision=192, meter=old_meter)
        finally:
            WORK.append(old_meter.operations)
        proof = OLD_CHECK.Meter()
        try:
            with self.assertRaises(ValueError):
                OLD_CHECK.verify_norm(program, cert, meter=proof)
        finally:
            WORK.append(proof.operations)

    def test_working_bit_cap_and_native_decimal_guard_remain(self):
        meter = C.INTERVAL.Meter()
        try:
            with self.assertRaises(OverflowError):
                meter.integer(1 << 16384)
            with self.assertRaises(OverflowError):
                meter.product(1 << 8192, 1 << 8192)
        finally:
            WORK.append(meter.operations)
        self.assertEqual(sys.get_int_max_str_digits(), 4300)

    def test_full_serialization_above_native4300_digits(self):
        program = vector('native_decimal_boundary_toy', [(2, F(1, 2**3700)),
                                                           (3, F(-1, 3**2300))], constant='0')
        cert, checked = replay(program, 0)
        self.assertTrue(checked['verified'])
        text = cert['periodic_energy']['integer_common_denominator']
        self.assertGreater(len(text), 4300)
        self.assertGreater(cert['counts']['peak_integer_bits'], 14285)
        with self.assertRaises(ValueError):
            int(text)
        self.assertEqual(C.format_exact(C.parse_exact(text)), text)
        for rational in (cert['periodic_energy']['V'], cert['tail']['upper']):
            self.assertEqual(C.format_exact(C.parse_exact(rational)), rational)
        for invalid in ('--1', '+1', '-0', '01', '1/01', '2/4', '1/-2', '0/2'):
            with self.assertRaises(ValueError):
                C.parse_exact(invalid)
        with self.assertRaises(OverflowError):
            C.format_exact(1 << 16384)
        with self.assertRaises(OverflowError):
            C.parse_exact('9'*5000)

    def test_prospective_memory_rejects_before_event_allocation(self):
        toy = vector('memory_toy', [(4995, F(1, 2))])
        estimate = C.memory_preflight([toy], 16)
        self.assertGreater(estimate, 2*1024**3)
        self.assertLess(estimate, 16*1024**3)
        large = vector('memory_guard_toy', [(2, F(2**4095, 3**2500)),
                                            (3, F(2**4094, 5**1700))], constant='0')
        with self.assertRaises(MemoryError):
            C.memory_preflight([large], C.INTERVAL.MAX_H)
        with self.assertRaises(ValueError):
            C.memory_preflight([toy], True)
        with self.assertRaises(ValueError):
            C.memory_preflight([toy], 16, workers=3)
        with self.assertRaises(ValueError):
            C.memory_preflight([vector('uncovered_step', [], steps=[(4099, 1)])], 16)

    def test_worker_api_and_coefficient_free_cache(self):
        first = C.audit_one({'program': vector('cache_toy_a', [(4098, F(1, 3))]), 'H': 2})
        second = C.audit_one({'program': vector('cache_toy_b', [(4098, F(-2, 5))],
                                                  constant='0'), 'H': 3})
        for result in (first, second):
            WORK.extend([result['producer_counts']['operations'], result['checker_operations']])
            self.assertTrue(result['verification']['verified'])
            self.assertFalse(result['verification']['convergence_proved'])
        self.assertGreater(second['certificate']['kernel_cache_hits'], 0)
        with self.assertRaises(ValueError):
            C.audit_one({'program': vector('extra_task_toy', []), 'H': 0, 'precision': 128})


if __name__ == '__main__':
    path = Path(__file__).with_name('floor_residual_capacity_050_development.json')
    if path.exists():
        raise SystemExit('retain prior focused receipt')
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(CapacityTests))
    receipt = {'schema': 'floor-capacity-050-synthetic-tests-v1', 'invocations': [{
        'returncode': 0 if result.wasSuccessful() else 1, 'tests': result.testsRun,
        'failures': len(result.failures), 'errors': len(result.errors),
        'elapsed_seconds': time.monotonic()-started,
        'operations': sum(WORK)+C._preflight_operations+C.CONVERSION_OPERATIONS,
        'conversion_operations': C.CONVERSION_OPERATIONS}],
        'scope': 'new synthetic capacity fixtures only; no actual scientific source or old suite replay',
        'limits': {'max_index': 5000, 'max_support': 4096, 'input_bits': 4096,
                   'working_bits': 16384, 'aggregate_bytes': 16*1024**3},
        'native_decimal_guard': sys.get_int_max_str_digits(),
        'actual_candidates_evaluated': False}
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt), flush=True)
    raise SystemExit(0 if result.wasSuccessful() else 1)
