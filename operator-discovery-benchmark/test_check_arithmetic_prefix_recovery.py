"""Tiny synthetic checks; no actual arithmetic source or candidate runs."""
from fractions import Fraction as Q
import unittest

import check_arithmetic_prefix_recovery as CHECK
from potential_candidate_language import Meter


METERS = [Meter(95000)]
WORK = METERS[0]


def limited_meter(limit, **kwargs):
    result = Meter(limit, **kwargs)
    METERS.append(result)
    return result


def number(value):
    return WORK.number(value)


def add(left, right):
    WORK.charge(3)
    return (number(left[0] + right[0]), number(left[1] + right[1]))


def scale(value, coefficient):
    WORK.charge(3)
    return (number(value[0] * coefficient), number(value[1] * coefficient))


ZERO = (Q(0), Q(0))
DIVISORS = [2, 3, 5]
SIGNAL = [ZERO, (Q(1), Q(2)), (Q(-2), Q(1)), (Q(3), Q(-1)),
          (Q(-1), Q(0)), (Q(0), Q(2)), (Q(2), Q(-3)),
          (Q(-2), Q(-1)), (Q(1), Q(1))]
COUNTS = [0, 0, 2, 1, 3, 0, 3, 1, 2]


def apply_signal(signal, counts=COUNTS):
    """Independent exact step-function operator on a synthetic complex signal."""
    WORK.live(100 + 8 * len(signal))
    output = [ZERO]
    for n in range(1, len(signal)):
        WORK.charge(3)
        size = counts[n]
        value = ZERO
        for divisor in DIVISORS[:size]:
            WORK.charge(3)
            coefficient = 1 if (n + divisor) % 2 == 0 else -1
            value = add(value, scale(signal[n // divisor], coefficient))
        output.append(scale(value, Q(1, size)) if size else ZERO)
    return output


def norm_squared(signal):
    """Integrate |signal|²/t² on [1,len(signal)] exactly, cell by cell."""
    total = Q(0)
    for n, value in enumerate(signal[1:], 1):
        WORK.charge(7)
        square = number(value[0] * value[0] + value[1] * value[1])
        weight = number(Q(1, n) - Q(1, n + 1))
        total = number(total + square * weight)
    return total


class RecoveryWitnessTests(unittest.TestCase):
    def test_exact_prime_gap_witness(self):
        self.assertEqual(CHECK.verify_witness([2, 3, 5], WORK),
                         dict(c='59/60', norm_bound='120', squared_bound='14400'))

    def test_arbitrary_integer_gap_and_late_gap(self):
        self.assertEqual(CHECK.verify_witness([3], WORK),
                         dict(c='5/6', norm_bound='12', squared_bound='144'))
        self.assertEqual(CHECK.verify_witness([2, 3, 4, 6], WORK),
                         dict(c='119/120', norm_bound='240', squared_bound='57600'))
        self.assertEqual(Q(CHECK.verify_witness([4096], WORK)['c']),
                         Q(1, 4096) + Q(1, 2))

    def test_no_gap_is_not_a_strict_infinite_tail_certificate(self):
        for witness in ([2], [2, 3], [2, 3, 4], list(range(2, 66))):
            with self.subTest(witness_length=len(witness)):
                with self.assertRaises(ValueError):
                    CHECK.verify_witness(witness, WORK)

    def test_strict_dilation_types_order_and_limits(self):
        invalid = [[], (2, 3, 5), [True, 3, 5], [2.0, 3, 5],
                   [1, 3, 5], [2, 3, 3], [3, 2, 5], [3, 4097],
                   list(range(3, 68))]
        for witness in invalid:
            with self.subTest(witness_type=type(witness).__name__):
                with self.assertRaises(ValueError):
                    CHECK.verify_witness(witness, WORK)
        maximal = list(range(2, 66))
        maximal[-1] = 66
        result = CHECK.verify_witness(maximal, WORK)
        self.assertLess(Q(result['c']), 1)

    def test_canonical_rational_parser(self):
        for text, expected in [('59/60', Q(59, 60)), ('0', Q(0)), ('-2', Q(-2))]:
            self.assertEqual(CHECK._rational(text, WORK), expected)
        for text in ['01', '2/4', '1/0', '1/-2', '+1', '-0', '1.0',
                     ' 1', 'true', '1/2/3', '9' * 1235, True]:
            with self.subTest(value_type=type(text).__name__):
                with self.assertRaises(ValueError):
                    CHECK._rational(text, WORK)

    def test_work_and_exact_bit_caps_are_preserved(self):
        small = limited_meter(1)
        with self.assertRaises(OverflowError):
            CHECK.verify_witness([2, 3, 5], small)
        self.assertEqual(small.operations, 1)
        narrow = limited_meter(1000, max_bits=8)
        with self.assertRaises(OverflowError):
            CHECK._rational('256', narrow)
        self.assertGreater(narrow.operations, 0)

    def test_nonmonotone_bank_complex_source_and_signed_selectors(self):
        result = CHECK.verify_witness(DIVISORS, WORK)
        applied = apply_signal(SIGNAL)
        self.assertLessEqual(norm_squared(applied),
                             number(Q(result['c']) * norm_squared(SIGNAL)))
        residual = [add(f, scale(a, -1)) for f, a in zip(SIGNAL, applied)]
        self.assertLessEqual(norm_squared(SIGNAL),
                             number(Q(result['squared_bound']) * norm_squared(residual)))

    def test_finite_delay_inverse_with_variable_counts(self):
        applied = apply_signal(SIGNAL)
        residual = [add(f, scale(a, -1)) for f, a in zip(SIGNAL, applied)]
        recovered = [ZERO] * len(SIGNAL)
        term = residual
        for _ in range(4):
            recovered = [add(f, a) for f, a in zip(recovered, term)]
            term = apply_signal(term)
        self.assertEqual(term, [ZERO] * len(SIGNAL))
        self.assertEqual(recovered, SIGNAL)

    def test_two_stage_bound_uses_same_horizon(self):
        c = CHECK.verify_witness(DIVISORS, WORK)
        first = [add(f, scale(a, -1))
                 for f, a in zip(SIGNAL, apply_signal(SIGNAL))]
        alternate = [0, 3, 0, 2, 1, 3, 0, 1, 3]
        second = [add(f, scale(a, -1))
                  for f, a in zip(first, apply_signal(first, alternate))]
        amplification = number(Q(c['squared_bound']) ** 2)
        self.assertLessEqual(norm_squared(SIGNAL),
                             number(amplification * norm_squared(second)))

    def test_measurable_bank_changes_inside_integer_cells(self):
        """The continuous theorem also permits a non-step bank, independently."""
        coefficient = Q(CHECK.verify_witness(DIVISORS, WORK)['c'])
        input_norm = output_norm = Q(0)
        for half_cell in range(2, 18):
            WORK.charge(12)
            left = Q(half_cell, 2)
            right = Q(half_cell + 1, 2)
            midpoint = number((left + right) / 2)
            n = int(midpoint)
            size = (half_cell * 3 + half_cell // 3) % 4
            value = ZERO
            for divisor in DIVISORS[:size]:
                WORK.charge(5)
                index = int(midpoint / divisor)
                sign = -1 if half_cell % 2 else 1
                value = add(value, scale(SIGNAL[index], sign))
            if size:
                value = scale(value, Q(1, size))
            weight = number(1 / left - 1 / right)
            input_square = number(SIGNAL[n][0] ** 2 + SIGNAL[n][1] ** 2)
            output_square = number(value[0] ** 2 + value[1] ** 2)
            input_norm = number(input_norm + input_square * weight)
            output_norm = number(output_norm + output_square * weight)
        self.assertLessEqual(output_norm, number(coefficient * input_norm))


def tearDownModule():
    operations = sum(meter.operations for meter in METERS)
    print('SYNTHETIC_WORK module=test_check_arithmetic_prefix_recovery operations=' + str(operations))


if __name__ == '__main__':
    unittest.main()
