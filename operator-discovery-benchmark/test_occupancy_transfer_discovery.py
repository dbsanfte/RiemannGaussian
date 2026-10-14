import unittest
from fractions import Fraction as Q

import occupancy_transfer_discovery as P


class Meter:
    operations = 0
    def charge(self, n):
        type(self).operations += n
    def live(self, n):
        pass


class OccupancyDiscoveryTests(unittest.TestCase):
    def test_fractional_grid_finds_unseeded_toy_modes(self):
        modes, rejected = P.spectral_search(['-1/2', '0', '1/2', '1'], Meter(), ((0, 2), (1, 4)))
        self.assertEqual(len(modes), 4)
        self.assertEqual(len(rejected), 12)
        for row in modes:
            f = list(map(Q, row['potential']))
            for mask in range(4):
                self.assertEqual(f[mask | 1], Q(row['eigen_u']) * f[mask])
                self.assertEqual(f[mask | 2], Q(row['eigen_v']) * f[mask])
        coefficients = P.recover(modes, [0, 0, 0, 1], Meter())
        self.assertIsNotNone(coefficients)
        self.assertEqual([sum(Q(c) * Q(row['potential'][i]) for c, row in zip(coefficients, modes))
                          for i in range(4)], [0, 0, 0, 1])

    def test_recovery_does_not_drop_outside_span(self):
        modes = [dict(potential=['1', '0']), dict(potential=['2', '0'])]
        self.assertIsNone(P.recover(modes, [0, 1], Meter()))
        answer = P.recover(modes, [3, 0], Meter())
        self.assertEqual(sum(Q(c)*Q(row['potential'][0]) for c, row in zip(answer, modes)), 3)
        self.assertEqual(P.canonical(['-1/2', '-3/4', '0']), [2, 3, 0])

    def test_target_keeps_birth_and_both_exit_channels(self):
        rows = P.compile_kernel(['0']*15 + ['1'], Meter())
        self.assertEqual(rows[15]['bulk'], ['-3', '2', '2'])
        self.assertEqual(rows[15]['left_exit'], ['2', '-1', '-1'])
        self.assertEqual(rows[15]['right_exit'], ['2', '-1', '-1'])
        self.assertEqual(rows[7]['bulk'], ['-1', '0', '1'])
        self.assertEqual(rows[7]['right_exit'], ['1', '0', '-1'])
        self.assertEqual(rows[0]['bulk'], ['0', '0', '0'])

    def test_kernel_polynomial_identity_for_fractional_potential(self):
        vector = [Q(i-7, 6) for i in range(16)]
        rows = P.compile_kernel(vector, Meter())
        for mask, row in enumerate(rows):
            # Use unrelated synthetic weights; this tests the formal identity,
            # not a fitted actual-prime sample.
            z = Q(2, 3)
            r, s = 1-z*z, 1-z**4
            values = P.kernel_counts(8, 3, 1, 5, Meter())
            evaluate = lambda c: Q(c[0]) + Q(c[1])*z*z + Q(c[2])*z**4
            direct = (vector[mask]*values['W']
                      -(r*vector[mask|1]+s*vector[mask|2])*values['W_L']
                      -(r*vector[mask|4]+s*vector[mask|8])*values['W_R'])
            expanded = (evaluate(row['bulk'])*values['W']
                        +evaluate(row['left_exit'])*values['left_exit']
                        +evaluate(row['right_exit'])*values['right_exit'])
            self.assertEqual(direct, expanded)

    def test_prefix_boundaries_by_integer_enumeration(self):
        for X, q, h, k in ((8,3,1,5), (8,3,5,1), (8,3,17,1), (1,2,1,1), (8,5,2,3)):
            found = P.kernel_counts(X, q, h, k, Meter())
            W = sum(h <= n and k <= n for n in range(X, 2*X))
            L = sum(q*h <= n and k <= n for n in range(X, 2*X))
            R = sum(h <= n and q*k <= n for n in range(X, 2*X))
            self.assertEqual(found, dict(W=W,W_L=L,W_R=R,left_exit=W-L,right_exit=W-R))

    def test_bernstein_conversion_and_certificate_scope(self):
        poly = [[0, '1'], [1, '-2'], [2, '1']]
        values = P.bernstein_coefficients(poly, Q(1,5), Q(4,5), Meter())
        self.assertEqual(values, [Q(16,25), Q(4,25), Q(1,25)])
        result = P.prove_bulk_envelope(poly, Meter())
        self.assertEqual(result['status'], 'CERTIFIED_ALGEBRAIC_BULK_ENVELOPE')
        failure = P.prove_bulk_envelope([[0,'-3'],[2,'2'],[4,'2']], Meter())
        self.assertEqual(failure['segments'], [])

    def test_fractional_weight_preserves_recovery_cost(self):
        self.assertEqual(P.weighted_polynomial('2','2','1/6'), [[0,'1'],[1,'-4'],[3,'2'],[5,'2']])
        with self.assertRaises(ValueError):
            P.weighted_polynomial('2','2','1/7')
        records = P.fractional_search([dict(eigen_u='1',eigen_v='0')], ['1/6'], Meter())
        self.assertEqual(records[0]['product_recovery_power'], '1/3')
        self.assertFalse(records[0]['original_target_recovered'])
        self.assertFalse(records[0]['energy_contraction_proved'])

    def test_individual_union_admission_rejects_degenerate_mixture(self):
        allowed = ['1' if mask & ~1 == 0 else '0' for mask in range(16)]
        other = ['1' if mask & ~4 == 0 else '0' for mask in range(16)]
        mixed = [str(Q(a)+Q(b)) for a,b in zip(allowed,other)]
        result = P.individual_union_modes([dict(id=0,potential=allowed),dict(id=1,potential=mixed)],Meter())
        self.assertEqual(result[0]['individual_union_eigenvalues'], ['1','0','0','0'])
        self.assertTrue(result[0]['scalar_phase_admissible'])
        self.assertFalse(result[1]['scalar_phase_admissible'])

    def test_phase_cone_affine_certificate_and_scope(self):
        fractional = [dict(id=0,polynomial=[[0,'1'],[2,'-1']],gamma='1/3',
                           eigen_u='1',eigen_v='0',product_recovery_power='2/3')]
        records = P.phase_search(fractional,['1/2'],Meter())
        self.assertEqual(records[0]['transformed_polynomial'], [[0,'1'],[2,'-8/7']])
        self.assertEqual(records[0]['sufficient_rho_bound'], '7/4')
        self.assertEqual(records[0]['certificate']['status'], 'CERTIFIED_ALGEBRAIC_BULK_ENVELOPE')
        self.assertFalse(records[0]['prime_free_projection_closure'])
        self.assertFalse(records[0]['arithmetic_operator_norm_proved'])


def tearDownModule():
    print('SYNTHETIC_WORK module=test_occupancy_transfer_discovery operations='+str(Meter.operations))


if __name__ == '__main__':
    unittest.main()
