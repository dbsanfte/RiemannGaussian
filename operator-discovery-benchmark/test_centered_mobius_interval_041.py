"""Synthetic checks only: no actual zeta normalization or source observations."""
import json
from fractions import Fraction as F
import unittest

from flint import arb, ctx
import centered_mobius_interval_041 as checker


def program(identifier='toy', m=2, lam='1/2', rho='0', delta='0', C='0'):
    return {'id': identifier, 'm': m, 'lambda': {'kind': 'rational', 'value': lam},
            'rho': rho, 'delta': delta, 'C': C}


def dyadic(pair):
    return F(int(pair[0]))*(F(2)**pair[1])


def covers(enclosure, value):
    return dyadic(enclosure['lower_dyadic']) <= value <= dyadic(enclosure['upper_dyadic'])


def toy_state(b=None, q=2, kappa=0):
    b = [0, 1]+[0]*62 if b is None else b
    return checker.center_from_coefficients(b, q, '2/3', kappa)


class SyntheticIntervalTests(unittest.TestCase):
    def test_prime_sieve_product_against_divisor_convolution(self):
        # Synthetic local values do not represent the actual r=1/3 source.
        def kernel(n):
            out, p = F(1), 2
            while p*p <= n:
                while n % p == 0:
                    out /= p+1
                    n //= p
                p += 1
            if n > 1:
                out /= n+1
            return out

        def mu(n):
            sign, p = 1, 2
            while p*p <= n:
                if n % p == 0:
                    n //= p
                    sign = -sign
                    if n % p == 0:
                        return 0
                p += 1
            return -sign if n > 1 else sign

        b = checker.independent_coefficients(60, '1/3', prime_power=lambda p: F(1, p+1))
        for n in range(1, 61):
            exact = sum((mu(d)*kernel(n//d) for d in range(1, n+1) if n % d == 0), F(0))
            with ctx.workprec(192):
                self.assertTrue(covers(checker.enclosure(b[n]), exact), n)
        self.assertEqual(b[0], 0)
        self.assertEqual(b[1], 1)

    def test_periodic_prefix_unit_and_index_zero(self):
        b = [0, 1, F(1, 2), F(-1, 4), F(3, 8), 2, -3]
        state = checker.center_from_coefficients(b, 3, '2/3', 0)
        B = [sum(b[:n+1]) for n in range(len(b))]
        for n in range(len(b)):
            self.assertEqual(state['J'][n], checker._ball(B[n]-3*B[n//3]))
        self.assertEqual(state['J'][1], 1)
        self.assertEqual(state['Dprefix'][1], 1)

    def test_continuous_centering_below_period(self):
        state = checker.center_from_coefficients([0, 1, 0, 0, 0, 0], 5, '1/2', F(2, 7))
        with ctx.workprec(192):
            self.assertTrue(covers(checker.enclosure(state['J'][1]), F(5, 7)))
            self.assertTrue(state['J'][2].overlaps(1-checker._ball(F(2, 7))*arb(2).sqrt()))
            self.assertTrue(state['J'][5].overlaps(-4-checker._ball(F(2, 7))*arb(5).sqrt()))

    def test_increment_prefix_has_all_heads(self):
        b = [0, 1, 2, -1, 3, 4, -2, 7]
        state = toy_state(b)
        total = F(0)
        for n in range(1, len(b)):
            cn = F(b[n])-(2*F(b[n//2]) if n % 2 == 0 else 0)
            total += cn*cn
            self.assertEqual(state['Dprefix'][n], checker._ball(total))

    def test_all_signed_moments_and_complete_variance(self):
        b = [0, 1, 2, -1, 3, 4, -2, 7, 0, -3, 1, 8, 0, 1, 2, 3]
        state = toy_state(b)
        p = program(lam='3/2', rho='1/2', delta='1/4', C='1')
        report = checker.audit(state, [p], {2: [2]})
        row = report['rows'][0]
        J = [F(0)]
        for n in range(1, len(b)):
            J.append(J[-1]+b[n]-(2*b[n//2] if n % 2 == 0 else 0))
        X, m, lam = 2, 2, F(3, 2)
        A = [sum(J[m*n+j] for j in range(m))/m for n in range(X, 2*X)]
        E_J = sum(J[n]**2 for n in range(X, 2*X))/X**2
        E_A = sum(x*x for x in A)/X**2
        C_JA = sum(J[n]*A[n-X] for n in range(X, 2*X))/X**2
        I = [A[n-X]-lam*J[n] for n in range(X, 2*X)]
        E_I = sum(x*x for x in I)/X**2
        C_JI = sum(J[n]*I[n-X] for n in range(X, 2*X))/X**2
        D = sum((J[k]-J[k-1])**2 for k in range(1, 2*m*X))/X
        E_child = sum(J[k]**2 for k in range(m*X, 2*m*X))/(m*X)**2
        V = sum((J[m*n+j]-A[n-X])**2 for n in range(X, 2*X) for j in range(m))/(m*X)**2
        Q = 2*lam*C_JI+F(5, 4)*E_I-(m*F(1, 2)-lam**2)*E_J-D
        expected = locals()
        for key in ('E_J', 'E_A', 'C_JA', 'E_I', 'C_JI', 'D', 'E_child', 'V', 'Q'):
            self.assertTrue(covers(row['moments'][key], expected[key]), key)
        self.assertEqual(E_child, E_A/m+V)
        self.assertEqual(row['complete_child_indices'], [4, 7])
        self.assertEqual(row['increment_indices'], [1, 7])
        self.assertTrue(row['complete_child_variance_identity_checked'])
        self.assertFalse(report['uniform_signed_bound_proved'])
        self.assertFalse(report['RH_proved'])
        json.dumps(report)

    def test_finite_pass_fail_and_exact_zero(self):
        state = toy_state()
        report = checker.audit(state, [program('pass', rho='1'), program('fail')], {2: [2]})
        self.assertEqual([x['status'] for x in report['rows']], ['pass', 'fail'])
        # Make J(2)=J(3)=0, and audit X=1, rho=0 so Q=E_A=0.
        state = toy_state([0, 1, 1, 0])
        self.assertEqual(checker.audit(state, [program()], {2: [1]})['rows'][0]['status'], 'pass')

    def test_uncertain_sign_is_unresolved(self):
        # Exact centered sequence is all zero after n=1, but uncertain injected
        # kappa gives a ball spanning both possible signs at a zero endpoint.
        state = toy_state([0, 1, 1, 0], kappa=arb('0 +/- 0.01'))
        row = checker.audit(state, [program()], {2: [1]})['rows'][0]
        self.assertEqual(row['status'], 'unresolved')
        self.assertLess(dyadic(row['moments']['Q']['lower_dyadic']), 0)
        self.assertGreater(dyadic(row['moments']['Q']['upper_dyadic']), 0)

    def test_gram_cache_reused_across_lambdas(self):
        state = toy_state()
        ps = [program(str(n), lam=str(n)) for n in range(4)]
        report = checker.audit(state, ps, {2: [1, 2, 4]})
        self.assertEqual(report['cached_base_grams'], 3)
        self.assertEqual(len(report['rows']), 12)
        before = state['meter'].operations
        checker.base_gram(state, 2, 4)
        self.assertEqual(state['meter'].operations, before)

    def test_source_lambda_symbolic_parameter_validation(self):
        p = program(m=3)
        p['lambda'] = {'kind': 'prime_power', 'prime': 3, 'exponent': '-1/3'}
        with ctx.workprec(192):
            result = checker.validate_program(p, '1/3')[1]
            self.assertTrue(result.overlaps(arb(3)**(-arb(1)/3)))
        for bad in ({'kind': 'prime_power', 'prime': 2, 'exponent': '-1/3'},
                    {'kind': 'prime_power', 'prime': 3, 'exponent': '-1/2'}):
            p['lambda'] = bad
            with self.assertRaises(ValueError):
                checker.validate_program(p, '1/3')
        p = program(m=4)
        p['lambda'] = {'kind': 'prime_power', 'prime': 4, 'exponent': '-1/3'}
        with self.assertRaises(ValueError):
            checker.validate_program(p, '1/3')

    def test_parameter_schema_rejections(self):
        for update in ({'m': True}, {'rho': '2'}, {'delta': '-1'}, {'C': '-1'}, {'rho': '2/4'}, {'extra': 0}):
            p = program()
            p.update(update)
            with self.assertRaises(ValueError):
                checker.validate_program(p, '1/3')
        p = program()
        p['lambda']['value'] = 0.5
        with self.assertRaises(ValueError):
            checker.validate_program(p, '1/3')

    def test_complete_horizon_and_scale_rejections(self):
        state = toy_state([0, 1, 0, 0, 0, 0, 0])
        with self.assertRaises(ValueError):
            checker.audit(state, [program()], {2: [2]})
        for scales in ([0], [True], [1, 1], []):
            with self.assertRaises(ValueError):
                checker.audit(state, [program()], {2: scales})
        with self.assertRaises(ValueError):
            checker.audit(state, [program(), program()], {2: [1]})

    def test_interval_serialization_has_exact_endpoints(self):
        with ctx.workprec(192):
            value = arb(1)/3
            bounds = checker.enclosure(value)
        self.assertTrue(covers(bounds, F(1, 3)))
        self.assertLess(dyadic(bounds['lower_dyadic']), dyadic(bounds['upper_dyadic']))

    def test_resource_caps_before_source_evaluation(self):
        with self.assertRaises(OverflowError):
            checker.center_from_coefficients([0, 1], 2, '2/3', 0, meter=checker.Meter(cap=0))
        with self.assertRaises(MemoryError):
            checker.Meter().reserve(checker.MAX_H, 4096)
        with self.assertRaises(ValueError):
            checker.build_state(True)
        with self.assertRaises(ValueError):
            checker.build_state(8, r_text='2/6')
        with self.assertRaises(ValueError):
            checker.build_state(8, precision=53)

    def test_no_float_or_missing_unit_in_synthetic_source(self):
        for b in ([0, 1.0], [1, 1], [0, 0]):
            with self.assertRaises(ValueError):
                checker.center_from_coefficients(b, 2, '2/3', 0)


if __name__ == '__main__':
    unittest.main()
