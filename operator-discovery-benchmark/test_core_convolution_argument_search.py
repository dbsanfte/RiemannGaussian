"""Exact calibration of new identities, domains and argument choices."""
import copy
import math
import unittest
from fractions import Fraction as Q

import core_convolution_argument_search as P
from prime_bank_candidates import Meter

METER = Meter(100000000, 300)


def B(n, d):
    return Q(n % d, d)-Q(d-1, 2*d)


def local_convolution(a, b):
    """Finite coefficient projection, independent of dense product support."""
    n = len(a)
    out = [Q(0)]*n
    for j in range(1, n+1):
        out[j-1] = sum((a[d-1]*b[j//d-1] for d in range(1, j+1) if j % d == 0), Q(0))
        METER.charge(j)
    return out


def polynomial_sequence(poly, variables, n):
    out = [Q(0)]*n
    for key, c in poly.items():
        term = [Q(1)]+[Q(0)]*(n-1)
        for name in key:
            term = local_convolution(term, variables[name])
        out = [a+c*b for a, b in zip(out, term)]
    return out


def root_floor(n, exponent):
    exponent = Q(exponent)
    return max(i for i in range(n+1) if i**exponent.denominator <= n**exponent.numerator)


class ConvolutionArgumentTests(unittest.TestCase):
    def test_floor_solution_is_exact_at_units_and_every_small_residue(self):
        result = P.synthesize_floor(METER)
        for a in range(1, 7):
            for d in range(1, 6):
                for n in range(2*a*d+1):
                    value = Q(0)
                    for term in result['certificate']['solution']:
                        b = result['basis'][term['column']]
                        x, y = b['denominator']; i, j = b['reciprocal']
                        value += Q(term['coefficient'])*B(n, a**x*d**y)/a**i/d**j
                        METER.charge(10)
                    self.assertEqual(value, B(n//d, a))

    def test_search_solves_coefficients_and_certifies_a_missing_basis(self):
        source, basis = P.floor_problem()
        columns = [P.decode(b['polynomial']) for b in reversed(basis)]
        solution = P.solve(columns, source, METER)
        self.assertEqual(P.compose(columns, solution['solution']), source)
        # Removing all product denominators prevents reconstruction of floor(n/(ad)).
        reduced = [P.decode(b['polynomial']) for b in basis if b['denominator'] != [1, 1]]
        failure = P.solve(reduced, source, METER)
        self.assertEqual(failure['status'], 'infeasible')
        y = P.decode(failure['dual'])
        self.assertTrue(all(sum(y.get(k, 0)*v for k, v in col.items()) == 0 for col in reduced))
        self.assertEqual(sum(y.get(k, 0)*v for k, v in source.items()), Q(failure['contradiction']))
        self.assertNotEqual(Q(failure['contradiction']), 0)

    def test_compiler_retains_actual_short_head_and_harmonic_null(self):
        a, h = [Q(3, 2), Q(-2, 3), Q(5, 7)], [Q(2), Q(-3), Q(1, 5), Q(4)]
        result = P.compile_dilation(a, h, P.synthesize_floor(METER), METER)
        v = list(map(Q, result['coefficients'])); c, C = Q(result['c']), Q(result['mean'])
        self.assertEqual(sum((x/i for i, x in enumerate(v, 1)), Q(0)), 0)
        self.assertNotEqual(1-C, 0)
        for n in range(13):
            periodic = sum((x*B(n, i) for i, x in enumerate(v, 1)), Q(0))
            direct = sum((hv*sum((av*B(n//d, i) for i, av in enumerate(a, 1)), Q(0))
                          for d, hv in enumerate(h, 1)), Q(0))
            self.assertEqual(periodic, direct)
            # Sum the coefficients of h*e directly, including e(1)=c-C.
            prefix = Q(0)
            for d, hv in enumerate(h, 1):
                for j in range(1, n//d+1):
                    ej = c-sum((av for i, av in enumerate(a, 1) if j % i == 0), Q(0))
                    if j == 1:
                        ej += 1-C
                    prefix += hv*ej
                    METER.charge(10)
            head = -(1-C)*sum(h[n:], Q(0))
            self.assertEqual(prefix, periodic+head)

    def test_invalid_floor_certificate_cannot_hide_in_specialized_arrays(self):
        result = P.synthesize_floor(METER)
        result['certificate']['solution'][0]['coefficient'] = '999'
        with self.assertRaises(ValueError):
            P.compile_dilation([0], [0], result, METER)

    def test_signed_gram_matches_period_averages_and_retains_subtraction(self):
        v, w = [Q(3, 2), Q(-7, 3), 2, -1], [1, -2, Q(5, 6), -3, 2]
        period = math.lcm(*range(1, 6))
        direct = sum((sum(Q(a)*B(n, i) for i, a in enumerate(v, 1))*
                      sum(Q(b)*B(n, j) for j, b in enumerate(w, 1))
                      for n in range(period)), Q(0))/period
        self.assertEqual(Q(P.exact_gram(v, w, METER)), direct)
        METER.charge(period*len(v)*len(w)*10)
        self.assertEqual(P.exact_gram([1], [1], METER), '0')
        self.assertNotEqual(Q(1, 12), 0)  # deleting the harmonic subtraction would give 1/12
        self.assertEqual(P.exact_gram([0, 1], [0, -1], METER), '-1/16')

    def test_divisor_search_improves_generic_power_and_only_arithmetic_logs(self):
        a = P.divisor_arguments(2, 0, 'mobius', METER)
        b = P.divisor_arguments(2, 0, 'bounded', METER)
        self.assertEqual(a['candidates'][a['selected']]['rule'], 'cutoff_divisor_cofactor')
        self.assertEqual(a['period_bound'], P.OLD.envelope(Q(5871, 4)*3**8, 3, logs=8))
        self.assertEqual(b['period_bound']['U_power'], '3')
        self.assertEqual(b['period_bound']['log_degree'], 10)
        self.assertEqual(a['window_bound'][1]['U_power'], '9')
        self.assertEqual(a['window_bound'][1]['log_degree'], 9)
        self.assertEqual(P.exponential_moment(6), 1957)

    def test_fractional_decay_crosses_critical_threshold_without_losing_logs(self):
        for decay, power, logs in [('1/6', '2', 8), ('1/3', '1', 8),
                                   ('1/2', '0', 9), ('2/3', '0', 0), ('3/2', '0', 0)]:
            result = P.divisor_arguments(2, decay, 'mobius', METER)
            self.assertEqual((result['period_bound']['U_power'], result['period_bound']['log_degree']), (power, logs))
        for depth in [0, 1, 3, 5]:
            result = P.divisor_arguments(depth, '1/6', 'mobius', METER)
            self.assertEqual(Q(result['period_bound']['U_power']), Q(2*(depth+1), 3))

    def test_geometry_grid_is_generated_from_rationals_not_nominated_examples(self):
        coarse, fine = P.geometry_grid(3), P.geometry_grid(6)
        self.assertTrue(set(coarse) < set(fine))
        self.assertIn(('1/6', '1/2'), fine)
        self.assertIn(('2/5', '5/6'), fine)
        self.assertEqual(len(fine), len(set(fine)))
        self.assertTrue(all(0 < Q(a) <= Q(b) < 1 and 2*Q(b) >= 1 for a, b in fine))
        self.assertEqual(max(Q(b) for a, b in fine), Q(5, 6))
        last = P.hyperbola_synthesize(*fine[-1], METER)
        self.assertTrue(last['one_e_coefficient'])
        self.assertEqual(P.geometry_cost(last, 2, '1/24')['coefficient_U_power'], 2)
        for bad in [1, 13, True, Q(3, 2)]:
            with self.assertRaises(ValueError):
                P.geometry_grid(bad)

    def test_hyperbola_identity_on_arbitrary_sequences_with_complete_mean_and_head(self):
        for alpha, beta in [('1/3', '1/2'), ('1/6', '1/2'), ('2/5', '2/3')]:
            result = P.hyperbola_synthesize(alpha, beta, METER)
            for n in [1, 8, 27]:
                e = [Q((-1)**j*(j % 5+1), j % 3+1) for j in range(1, n+1)]
                t, r = root_floor(n, alpha), root_floor(n, beta)
                variables = dict(C=[Q(7, 3)]+[Q(0)]*(n-1), e=e,
                                 t=e[:t]+[Q(0)]*(n-t), r=e[:r]+[Q(0)]*(n-r))
                source = polynomial_sequence(P.decode(result['source']), variables, n)
                h = polynomial_sequence(P.decode(result['one_e_coefficient']), variables, n)
                z = polynomial_sequence(P.decode(result['finite_head']), variables, n)
                joined = [a+b for a, b in zip(local_convolution(h, e), z)]
                self.assertEqual(source, joined)
                self.assertEqual(polynomial_sequence(P.decode(result['vanishing_remainder']), variables, n), [0]*n)
                self.assertEqual(source[0], (Q(7, 3)+e[0])**3)
            self.assertFalse(result['global_Dirichlet_series_identity'])
            self.assertFalse(result['moving_cutoffs_allowed_in_period_rule'])
            self.assertFalse(result['head_or_cross_paid'])

    def test_every_hyperbola_threshold_has_a_primal_or_dual_certificate(self):
        result = P.hyperbola_synthesize('1/3', '1/2', METER)
        source, basis, costs, ideals, _ = P.geometry_problem('1/3', '1/2')
        self.assertEqual(result['trials'][result['selected']]['support_threshold'], '5/6')
        for trial in result['trials']:
            columns = [basis[i] for i in trial['allowed']]+ideals
            cert = trial['certificate']
            if cert['status'] == 'feasible':
                self.assertEqual(P.compose(columns, cert['solution']), source)
            else:
                y = P.decode(cert['dual'])
                self.assertTrue(all(sum(y.get(k, 0)*v for k, v in column.items()) == 0 for column in columns))
                self.assertNotEqual(sum(y.get(k, 0)*v for k, v in source.items()), 0)

    def test_spacing_failure_keeps_mean_unit_and_does_not_refute_arithmetic(self):
        g = P.hyperbola_synthesize('1/3', '1/2', METER)
        cost = P.geometry_cost(g, 2, '1/24')
        self.assertEqual(cost['coefficient_U_power'], 2)
        self.assertEqual(cost['normalized_spacing_cost_power'], '25/24')
        self.assertEqual(cost['optimistic_zero_amplitude_cost_power'], '7/8')
        self.assertFalse(cost['actual_arithmetic_lower_bound'])
        self.assertFalse(cost['finite_head_and_cross_paid'])
        self.assertFalse(cost['outer_kernel_and_centering_paid'])

    def test_prime_obstruction_uses_exact_factor_multiplicity_and_narrow_scope(self):
        for p in range(5):
            k = p+1
            result = P.fresh_prime_obstruction(p)
            factors = {(str(i),): Q(-1) for i in range(k)}
            expanded = P.power(factors, k)
            self.assertEqual(expanded[tuple(str(i) for i in range(k))], Q(result['coefficient']))
            self.assertEqual(Q(result['lower_coefficient']), Q(math.factorial(k)**2, 24))
            self.assertFalse(result['finite_window_lower_bound'])
            self.assertFalse(result['full_core_refuted'])
            self.assertEqual(result['asymptotic']['imported_theorem'], 'pi(x)~x/log(x)')

    def test_invalid_domains_and_resource_exhaustion_do_not_prove_claims(self):
        for p, decay, profile in [(-1, 0, 'mobius'), (13, 0, 'mobius'), (2, '-1/2', 'mobius'), (2, 0, 'unknown')]:
            with self.assertRaises(ValueError):
                P.divisor_arguments(p, decay, profile, METER)
        for a, b in [('0', '1/2'), ('2/3', '1/3'), ('1/2', '3/2')]:
            with self.assertRaises(ValueError):
                P.hyperbola_synthesize(a, b, METER)
        with self.assertRaises(OverflowError):
            P.synthesize_floor(Meter(0, 60))


def tearDownModule():
    print('operations='+str(METER.operations))


if __name__ == '__main__':
    unittest.main()
