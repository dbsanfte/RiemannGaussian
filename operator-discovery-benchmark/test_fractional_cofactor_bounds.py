import unittest
from fractions import Fraction as F

import fractional_cofactor_bounds as P


def frontier():
    # Synthetic signed prime profile -2*p^(-1/6)+p^(-2/3), with unit3.
    return dict(state=0, r='1/6', unit_ceiling='3', coefficient_ceiling='3',
        prime_polynomial=[[1, '-2', '0'], [4, '1', '0']],
        sign=-1, coefficient_floor='2', q_threshold='1/2',
        energy_upper_exponent='2/3')


class FractionalBounds(unittest.TestCase):
    def test_large_denominator_is_a_real_twist(self):
        c = P.candidate(frontier(), '1/257')
        self.assertEqual(c['prime_powers'][0][0], str(F(1, 6)+F(1, 257)))
        self.assertEqual(c['program']['exponent'], '1/257')
        self.assertEqual(c['recovery']['energy_upper']['power'], '2/3')

    def test_fractional_gain_is_priced_back(self):
        c = P.candidate(frontier(), '2/5')
        self.assertLess(F(c['energy_upper']['power']), 0)
        self.assertEqual(c['recovery']['recovered_power_gain'], '0')
        self.assertFalse(c['whole_signed_bound_proved'])

    def test_log_boundary_and_summable_region(self):
        edge = P.candidate(frontier(), '5/6')
        beyond = P.candidate(frontier(), '7/8')
        self.assertEqual(edge['prefix_upper']['log_power'], 1)
        self.assertEqual(beyond['prefix_upper']['log_power'], 0)
        self.assertGreater(F(beyond['recovery']['energy_upper']['power']), F(2, 3))

    def test_exact_inputs_and_duplicate_normalization(self):
        with self.assertRaises(ValueError):
            P.candidate(frontier(), 0.2)
        with self.assertRaises(ValueError):
            P.candidate(frontier(), '-1/5')
        with self.assertRaises(ValueError):
            P.search(dict(source={}, states=[], frontier_bounds=[frontier()]), ['1/5', '2/10'])


if __name__ == '__main__':
    unittest.main()
