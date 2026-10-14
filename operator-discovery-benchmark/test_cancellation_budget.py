import unittest
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_budget as B


class Tests(unittest.TestCase):
    def test_formal_constant_is_not_x1_substitution(self):
        instance = dict(target='mu', horizon=2, lhs=L.dump_poly(L.constant(20)),
                        square_groups=[[dict(weight='2', poly=L.dump_poly(L.add(L.variable(1), L.constant(3))))]],
                        relation_groups=[[dict(spec=dict(kind='unit'), multiplier=L.dump_poly(L.variable(1)))],
                                         [dict(spec=dict(kind='norm', n=2, factors=[[2, 1]]), multiplier=L.dump_poly(L.constant(4)))]] )
        result = B.extract(instance, dict(square_weights=['1/2'], relation_weights=['100', '-2']))
        self.assertEqual(result['B'], '17')
        self.assertEqual(result['scalar_slack'], '3')
        self.assertFalse(result['nonconstant_identity_verified'])
        with self.assertRaises(ValueError): B.audit_added_zero_scalars(instance, 0, 0)

    def test_zero_constant_multiplier_does_not_create_scalar(self):
        instance = dict(target='mu', horizon=2, lhs=[], square_groups=[], relation_groups=[[
            dict(spec=dict(kind='norm', n=2, factors=[[2, 1]]), multiplier=L.dump_poly({(1, 2): F(1)}))]])
        self.assertEqual(B.extract(instance, dict(square_weights=[], relation_weights=['5']))['B'], '0')
        self.assertTrue(B.audit_added_zero_scalars(instance, 0, 0)['all_added_scalars_zero'])


if __name__ == '__main__': unittest.main()
