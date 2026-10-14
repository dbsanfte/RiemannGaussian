"""Generic signed telescoping and proof-search calibrations; no source samples."""
import unittest
from fractions import Fraction as Q

import core_signed_primitive_search as P
from prime_bank_candidates import Meter

METER = Meter(500000000, 600)
HEIGHTS = {k: {'bound': P.MOM.envelope(0)} for k in range(13)}


class SignedPrimitiveTests(unittest.TestCase):
    def test_polynomial_family_rediscovers_uniform_signed_reciprocal_control(self):
        for degree in range(7):
            source = {tuple(sorted(('a', 'x')+('c',)*degree)): Q(1)}
            result = P.synthesize(source, Q(9, 20), HEIGHTS, P.MOM.envelope(0), METER)
            self.assertEqual(result['baseline'], P.MOM.envelope(0, 1))
            self.assertTrue(result['requested_bound_proved'])
            self.assertEqual(P.MOM.decode(result['certificate']['potential']),
                             {('c',)*(degree+1): Q(1, degree+1)})
            self.assertEqual(result['certificate']['bound'], P.MOM.envelope(0))
            # Every higher finite-difference term has at least two 1/q factors.
            self.assertTrue(all(row['monomial'].count('a') >= 2 for row in result['certificate']['residual']))

    def test_mixed_polynomial_coefficients_are_solved_not_nominated(self):
        source = {('a', 'x'): Q(1, 6), ('a', 'c', 'x'): Q(-3), ('a', 'c', 'c', 'c', 'x'): Q(2)}
        result = P.synthesize(source, Q(2, 3), HEIGHTS, P.MOM.envelope(0), METER)
        self.assertEqual(P.MOM.decode(result['certificate']['potential']),
                         {('c',): Q(1, 6), ('c', 'c'): Q(-3, 2), ('c',)*4: Q(1, 2)})
        self.assertTrue(result['requested_bound_proved'])

    def test_primitive_basis_handles_real_and_complex_conjugate_orbits(self):
        source = {('Abar', 'b', 'x'): Q(1), ('A', 'bbar', 'x'): Q(1)}
        self.assertEqual(P.primitive_basis(source, METER), [{('A', 'Abar'): Q(1)}])
        result = P.synthesize(source, Q(1, 3), HEIGHTS, P.MOM.envelope(0), METER)
        self.assertFalse(result['requested_bound_proved'])
        self.assertEqual(result['certificate']['bound'], P.MOM.envelope(Q(4, 3)))

    def test_zero_mobius_head_is_retained_after_exact_signed_elimination(self):
        primitive = {('A', 'Dbar'): Q(1), ('Abar', 'D'): Q(1)}
        change = P.delta(primitive, METER)
        source = {k: v for k, v in change.items() if 'x' in k}
        result = P.synthesize(source, Q(9, 20), HEIGHTS, P.MOM.envelope(0), METER)
        exact = result['unconstrained_signed_elimination']
        self.assertEqual(exact['status'], 'feasible')
        self.assertEqual(P.MOM.decode(exact['certificate']['residual']),
                         {('A', 'bbar'): Q(-1), ('Abar', 'b'): Q(-1)})

    def test_unit_endpoint_and_invariant_zeta_cost_remain(self):
        polynomial = {('c', 'c', 'z', 'zbar'): Q(1)}
        value = P.initialized(polynomial, METER)
        self.assertEqual(value, {('c', 'c', 'z', 'zbar'): Q(1), ('z', 'zbar'): Q(-1)})
        heights = {2: {'bound': P.MOM.envelope(Q(1, 6), 1)}}
        self.assertEqual(P.bound(value, Q(9, 20), heights, True), P.MOM.envelope(Q(1, 6), 1))

    def test_event_dependent_storage_coefficient_is_rejected(self):
        with self.assertRaises(ValueError):
            P.delta({('a', 'c'): Q(1)}, METER)

    def test_ternary_reduction_and_conjugation(self):
        value = P.delta({('c',)*4: Q(1)}, METER)
        self.assertEqual(value, {('a', 'c', 'c', 'c', 'x'): Q(4),
            ('a', 'a', 'c', 'c', 'x', 'x'): Q(6), ('a', 'a', 'a', 'c', 'x'): Q(4),
            ('a', 'a', 'a', 'a', 'x', 'x'): Q(1)})

    def test_canonical_E_relation_is_collected_before_search(self):
        polynomial = {('E',): Q(1), (): Q(-1), ('c', 'z'): Q(-1), ('A', 'z'): Q(1)}
        self.assertEqual(P.canonical(polynomial, METER), {})

    def test_inconsistent_system_has_a_nonzero_exact_left_null_witness(self):
        columns = [{('a',): Q(1), ('b',): Q(1)}]
        source = {('a',): Q(1), ('b',): Q(2)}
        result = P.linear_solve(columns, source, sorted(source), [0], METER)
        self.assertEqual(result['status'], 'infeasible')
        witness = P.MOM.decode(result['dual'])
        self.assertEqual(sum(witness.get(k, 0)*v for k, v in columns[0].items()), 0)
        self.assertEqual(sum(witness.get(k, 0)*v for k, v in source.items()), Q(result['contradiction']))
        self.assertNotEqual(Q(result['contradiction']), 0)

    def test_free_columns_and_missing_target_rows_are_not_silently_dropped(self):
        columns = [{('a',): Q(2)}, {('a',): Q(3)}]
        result = P.linear_solve(columns, {('a',): Q(1)}, [('a',)], [0, 1], METER)
        self.assertEqual(result['solution'], [{'basis_id': 0, 'coefficient': '1/2'}])
        result = P.linear_solve(columns, {('c',): Q(1)}, [('c',)], [0, 1], METER)
        self.assertEqual(result['status'], 'infeasible')

    def test_critical_event_cost_and_fractional_contour_exponents(self):
        self.assertEqual(P.term_cost(('a', 'c', 'x'), Q(1, 6), HEIGHTS), P.MOM.envelope(0, 1))
        self.assertEqual(P.term_cost(('A', 'b', 'x'), Q(1, 6), HEIGHTS), P.MOM.envelope(Q(5, 3)))
        with self.assertRaises(ValueError):
            P.term_cost(('z',), Q(1, 6), {})

    def test_generic_complete_source_restatement_is_not_a_paid_boundary(self):
        transition = P.ALG.compile_transition(1, 2, True, METER)
        source = P.joined_source(transition, METER)
        result = P.synthesize(source, Q(1, 3), HEIGHTS, P.MOM.envelope(0), METER)
        exact = result['unconstrained_signed_elimination']
        self.assertEqual(exact['status'], 'feasible')
        polynomial = P.canonical(P.MOM.decode(transition['parent']), METER)
        energy = P.ALG.multiply(polynomial, P.ALG.conjugate(polynomial), METER)
        self.assertEqual(P.MOM.decode(exact['certificate']['boundary']), P.initialized(energy, METER))
        self.assertFalse(result['requested_bound_proved'])
        self.assertGreater(Q(exact['certificate']['endpoint_bound']['B_power']), 0)


def tearDownModule():
    print('operations='+str(METER.operations))


if __name__ == '__main__':
    unittest.main()
