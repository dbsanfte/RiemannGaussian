"""Branch/invariant tests, not asymptotic speed or coverage evidence."""
import unittest
from fractions import Fraction
from math import comb

import factor_network
from factor_solver import (count_network_with_layout, direct_factor, factor,
                           recover_from_counter)
from shared_parameters import (Parameters, binomial_tail, ceil_log2, check_guard,
                               scheduled_guard, scope_statistics)


class ParameterTests(unittest.TestCase):
    def test_exact_log_endpoints(self):
        self.assertEqual([ceil_log2(n) for n in (1, 2, 3, 4, 5, 8, 9)],
                         [0, 1, 2, 2, 3, 3, 4])

    def test_streamed_tail_against_closed_form(self):
        for r, Q, A0, R in ((2, 5, 0, 4), (3, 7, 2, 3), (5, 10, 1, 7)):
            a, b = binomial_tail(r, Q, A0, R)
            expected = sum(Fraction(comb(Q, k) * (r-1)**k * (r+1)**(Q-k),
                                    (2*r)**Q)
                           for k in range(Q+1) if not A0 <= k < A0+R)
            self.assertEqual(Fraction(a, b), expected)

    def test_all_guard_terms(self):
        p = Parameters(2, 5, 4, 0, 2)
        # This only tests the exact generic guard, not a useful cost exponent.
        self.assertTrue(check_guard(2**23, 2**24, 2, 2, p).accepted)
        self.assertIn("incidence load balance", check_guard(100, 200, 2, 2, p).reasons)
        bad_tail = Parameters(2, 5, 1, 5, 2)
        self.assertIn("binomial spectral tail",
                      check_guard(2**23, 2**24, 2, 2, bad_tail).reasons)
        self.assertFalse(scheduled_guard(100, 200, 2, 2).accepted)

    def test_actual_scope_statistics(self):
        net = factor_network.compile(15)
        s = scope_statistics(len(net.edges), tuple(v.ports for v in net.vertices))
        self.assertEqual(s['incidence'], 2*s['n'])
        self.assertEqual(s['occurrence'], 2)
        with self.assertRaises(ValueError):
            scope_statistics(2, [(0, 0), (1,)])


class RecoveryTests(unittest.TestCase):
    def test_live_counter_adapter_and_recovery(self):
        # A small direct multiplication network tests the actual counter adapter.
        # It is an interface control, not the macro-FFT asymptotic construction.
        from types import SimpleNamespace
        from shared_counter import ExplicitDesign

        class TinyNetwork:
            N = 6
            edges = tuple(range(4))
            input_bits = {'P': (0, 1), 'Q': (2, 3)}

            def __init__(self, fixed=None):
                self.fixed = dict(fixed or {})

                def multiplication(bits):
                    P, Q = bits[0]+2*bits[1], bits[2]+2*bits[3]
                    return int(P >= 2 and Q >= 2 and P*Q == self.N and
                               all(bits[e] == b for e, b in self.fixed.items()))

                self.vertices = (SimpleNamespace(ports=tuple(range(4)),
                                                 entry=multiplication),) + tuple(
                    SimpleNamespace(ports=(e,), entry=lambda _: 1) for e in range(4))

            def restrict(self, fixed):
                return TinyNetwork(self.fixed | fixed)

        net = TinyNetwork()
        nodes = range(1, 10)
        forms = {(f, v): {v: (1,)} for f, vertex in enumerate(net.vertices)
                 for v in vertex.ports}
        design = ExplicitDesign(4, 2, 9, 1, 1,
            {t: ((0, 1), (2, 3)) for t in nodes},
            {t: (0,)*len(net.vertices) for t in nodes},
            {t: ((), ((1, 0), (0, 1))) for t in nodes}, forms)
        answer, queries = recover_from_counter(
            net, lambda restricted: count_network_with_layout(restricted, design))
        self.assertEqual(answer, (2, 3))
        self.assertEqual(queries, 3)

    @staticmethod
    def diagnostic_counter(net):
        # Independent exact contraction through the previously audited bijection.
        # Deliberate small-control-only divisor enumeration: NOT the fast counter.
        return sum(net.witness(p, net.N//p)['valid']
                   for p in range(2, net.N) if net.N % p == 0)

    def test_conditional_recovery_and_query_count(self):
        net = factor_network.compile(15)
        answer, queries = recover_from_counter(net, self.diagnostic_counter)
        self.assertIn(answer, ((3, 5), (5, 3)))
        self.assertEqual(queries, net.parameters['L']+1)

    def test_square_and_empty(self):
        self.assertEqual(recover_from_counter(factor_network.compile(9),
                                             self.diagnostic_counter)[0], (3, 3))
        self.assertEqual(recover_from_counter(factor_network.compile(7),
                                             self.diagnostic_counter), (None, 1))

    def test_counter_error_is_not_silently_masked(self):
        with self.assertRaises(ArithmeticError):
            recover_from_counter(factor_network.compile(15), lambda _: -1)
        responses = iter((1, 2))
        with self.assertRaises(ArithmeticError):
            recover_from_counter(factor_network.compile(15), lambda _: next(responses))

    def test_uniform_wrapper_reports_fallback(self):
        result = factor(15)
        self.assertEqual(result.factors, (3, 5))
        self.assertEqual(result.count_queries, 0)
        self.assertEqual(result.method, "direct finite-size fallback")
        self.assertTrue(result.guard_reasons)
        self.assertIsNone(direct_factor(2))


if __name__ == '__main__':
    unittest.main()
