from copy import deepcopy
import unittest
import fractional_prime_kernel_search_051 as P
import check_fractional_prime_kernel_values_051 as C

M = C.Meter(cap=100_000_000)
PM = P.Meter()
REQUEST = {'a': '12/17', 'b': '5/17', 'alpha': '13/29', 'sign': -1}


class ValueTests(unittest.TestCase):
    def row(self, request=REQUEST, n=18):
        return P.evaluate(request, n, meter=PM)

    def test_independent_divisors_prime_powers_and_zero_unit(self):
        for n in (1, 12, 18, 42):
            v = C.verify_value(REQUEST, n, self.row(n=n), M)
            self.assertTrue(v['verified'])
            self.assertFalse(v['uniform_bound_proved'])

    def test_fractional_zero_base_and_exact_polynomial_endpoints(self):
        for request in ({'a': '1', 'b': '0', 'alpha': '7/19', 'sign': -1},
                        {'a': '5/17', 'b': '12/17', 'alpha': '1', 'sign': 1},
                        {'a': '5/17', 'b': '12/17', 'alpha': '2', 'sign': 1}):
            C.verify_value(request, 18, self.row(request), M)

    def test_factorization_mu_and_log_argument_mutations(self):
        for mutate in (lambda r: r['factorization'][0].update(exponent=2),
                       lambda r: r.update(ordinary_mu_n=1),
                       lambda r: r['squarefree_divisors'][1].update(mu=1),
                       lambda r: r['squarefree_divisors'][1].update(log_arguments=[2, 8])):
            row = self.row(); mutate(row)
            with self.assertRaises(ValueError): C.verify_value(REQUEST, 18, row, M)

    def test_wrong_value_and_global_claim_rejected(self):
        row = self.row(); row['value']['lower_dyadic'] = ['2', 0]; row['value']['upper_dyadic'] = ['3', 0]
        with self.assertRaises(ValueError): C.verify_value(REQUEST, 18, row, M)
        row = self.row(); row['uniform_bound_proved'] = True
        with self.assertRaises(ValueError): C.verify_value(REQUEST, 18, row, M)

    def test_binding_precision_and_typed_parameters(self):
        for change in ({'n': True}, {'precision': 256}, {'strict_positive': 1}):
            row = self.row(); row.update(change)
            with self.assertRaises(ValueError): C.verify_value(REQUEST, 18, row, M)
        row = self.row(); row['request'] = dict(REQUEST, alpha='14/29')
        with self.assertRaises(ValueError): C.verify_value(REQUEST, 18, row, M)

    def test_dyadic_and_resource_guards(self):
        for pair in (['1', True], ['01', 0], ['1', 16385], ['1'*1301, 0]):
            with self.assertRaises(ValueError): C._dyadic(pair)
        with self.assertRaises(OverflowError):
            C.verify_value(REQUEST, 18, self.row(), C.Meter(cap=0))
        with self.assertRaises(ValueError): C.verify_value(REQUEST, 2**32, self.row(), M)


def tearDownModule():
    print('SYNTHETIC_WORK checker=%d fixture=%d' % (M.operations, PM.operations))


if __name__ == '__main__':
    unittest.main()
