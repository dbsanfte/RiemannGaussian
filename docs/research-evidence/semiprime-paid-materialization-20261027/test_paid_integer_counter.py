"""Differential algebra/control tests, not semiprime scaling evidence."""
import unittest
from fractions import Fraction as F
from unittest.mock import patch
import paid_integer_counter as paid

ref = paid.reference()


def design(copies=1):
    forms = {}
    for e in range(copies):
        forms[e, 0] = {0: (1, F(-1, 2)), 1: (0, F(1, 2))}
        forms[e, 1] = {0: (0, F(1, 3)), 1: (1, F(-1, 3))}
    return ref.ExplicitDesign(2, 2, 2, 1, 1,
        {1: ((0,), (1,)), 2: ((0,), (1,))},
        {1: (0,)*copies, 2: (0,)*copies},
        {1: ((), ((1,),)), 2: ((), ((1,),))}, forms)


class PaidCounterTests(unittest.TestCase):
    def test_all_binary_truth_tables(self):
        for mask in range(16):
            f = ref.Factor((0, 1), lambda b, m=mask: (m >> (b[0]+2*b[1])) & 1)
            with patch.object(ref, 'direct_count', side_effect=AssertionError('diagnostic forbidden')):
                got = paid.count(2, [f], design())
            self.assertEqual(got['value'], mask.bit_count())
            self.assertEqual(got['value'], ref.count(2, [f], design()).value)
            self.assertEqual(got['counts']['original_predicate_calls'], 4)
            self.assertEqual(got['source_denominator'], 6)
            self.assertEqual(got['maximum_declared_degree'], 2)

    def test_product_higher_precision_and_prefix_restriction(self):
        factors = [ref.Factor((0, 1), lambda b: b[0] ^ b[1]),
                   ref.Factor((0, 1), lambda b: b[0])]
        got = paid.count(2, factors, design(2))
        self.assertEqual(got['value'], 1)
        self.assertEqual(got['value'], ref.count(2, factors, design(2)).value)
        self.assertEqual(got['J'], 3)
        self.assertEqual(got['maximum_declared_degree'], 4)
        self.assertEqual(got['counts']['original_predicate_calls'], 8)

    def test_empty_factors_and_zero_arity(self):
        d = ref.ExplicitDesign(2, 2, 2, 1, 1,
            {1: ((0, 1), ()), 2: ((0, 1), ())},
            {1: (), 2: ()}, {1: ((), ()), 2: ((), ())}, {})
        self.assertEqual(paid.count(2, [], d)['value'], 4)
        d.sigma = {1: (1,), 2: (1,)}
        self.assertEqual(paid.count(2, [ref.Factor((), lambda _: 0)], d)['value'], 0)
        self.assertEqual(paid.count(2, [ref.Factor((), lambda _: 1)], d)['value'], 4)

    def test_nonboolean_table_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Boolean'):
            paid.count(2, [ref.Factor((0, 1), lambda _: F(1, 2))], design())

    def test_invalid_source_rejected(self):
        d = design()
        d.measurements = {1: ((), ()), 2: ((), ())}
        with self.assertRaisesRegex(ValueError, 'kernel'):
            paid.count(2, [ref.Factor((0, 1), lambda b: b[0])], d)

    def test_homogeneous_tensor_nonboolean_ports(self):
        meter = paid.Meter()
        ops = paid.HomogeneousJets(3, 6, 3, meter)
        ports = [ops.make((9, 2, -4), 1), ops.make((-3, 5, 1), 1), ops.make((7, -1, 2), 1)]
        r_ops = ref.Jets(3, ref.Stats())
        for table in ((0, 1, 1, 0, 1, 0, 0, 1), (1,)*8, (0,)*8):
            f = ref.Factor((0, 1, 2), lambda b: table[b[0]+2*b[1]+4*b[2]])
            expected = ref.multilinear_extension(f, [ops.decode(p) for p in ports], r_ops, r_ops.stats)
            got = ops.tensor(table, ports)
            self.assertEqual(ops.decode(got), expected)
            self.assertEqual(got.degree, 3)
        with self.assertRaises(ValueError):
            ops.add(ops.const(0), ops.const(0, 1))

    def test_input_only_fallback_smoke(self):
        # Entry-point wiring only; no timing or asymptotic evidence.
        out = paid.factor(15)
        self.assertEqual(out['method'], 'finite_guard_fallback')
        self.assertEqual(out['factors'][0] * out['factors'][1], 15)
        self.assertEqual(out['count_queries'], 0)


if __name__ == '__main__':
    unittest.main(verbosity=2)
