"""New integration tests for inference, exact proof programs and open leaves."""
import copy
from fractions import Fraction as Q
import unittest
import prime_transfer_search_058 as S
import prime_transfer_algebra_058 as A
import check_prime_transfer_058 as C

SM = S.Meter()
CM = C.Meter(cap=1_000_000_000, seconds=600)


def fixture():
    universe = [2, 7]
    atoms = A.grammar(universe, SM, max_attenuation_degree=1)['atoms']
    pos = {(tuple(a['primes']), a['divisor'], a['attenuation']): i for i, a in enumerate(atoms)}
    rows = []
    for p, other in [(2, 7), (7, 2)]:
        vector = ['0']*len(atoms)
        for key, value in {((2, 7), 1, 1): 1, ((other,), 1, 1): -1,
            ((other,), 1, p): 1, ((2, 7), p, p): -1}.items(): vector[pos[key]] = str(value)
        rows.append({'coefficients': vector})
    return universe, atoms, rows


class SearchTests(unittest.TestCase):
    def test_pair_elimination_discovers_signed_transfer(self):
        u, atoms, basis = fixture()
        promoted = S.promote(atoms, basis, SM)
        found = [r for r in promoted['rows'] if S.identify_exchange(u, atoms, r, SM)['family'] == 'weighted_prime_exchange']
        self.assertEqual(len(found), 1)
        row = found[0]
        self.assertEqual(row['origin']['kind'], 'pair_current_elimination')
        self.assertTrue(row['signed_lower_terms'])
        self.assertTrue(C.verify_identity(S.request(u, atoms, row), CM)['verified'])
        self.assertEqual(sorted(atoms[i]['divisor'] for i in row['lower_columns']), [2, 7])

    def test_all_presence_orders_and_independent_gate(self):
        u, atoms, basis = fixture()
        row = next(r for r in S.promote(atoms, basis, SM)['rows'] if r['origin']['kind'] == 'pair_current_elimination')
        req = S.request(u, atoms, row, True)
        cert = S.order_certificate(req, SM)
        self.assertEqual(cert['order'], 2)
        cases = {tuple(c['presence']): c for c in cert['cases']}
        self.assertIsNone(cases[(0, 0)]['order'])
        self.assertEqual(cases[(1, 1)]['order'], 3)
        self.assertEqual(set(cases), {(0, 0), (1, 0), (0, 1), (1, 1)})
        self.assertTrue(C.verify_source_order(req, cert, CM)['verified'])
        damaged = copy.deepcopy(cert); damaged['order'] = 3
        with self.assertRaises(ValueError): C.verify_source_order(req, damaged, CM)

    def test_general_fractional_endpoint_and_open_forcing(self):
        u, atoms, basis = fixture()
        row = next(r for r in S.promote(atoms, basis, SM)['rows'] if r['origin']['kind'] == 'pair_current_elimination')
        req = S.request(u, atoms, row, True); order = S.order_certificate(req, SM)
        cert = S.endpoint_program(req, order, '1/257', '257/1026', '2/5')
        self.assertEqual(cert['microscopic']['N_power'], '1/2')
        self.assertEqual(cert['tail']['N_power'], '3/5')
        verified = C.verify_endpoint_bound(cert['request'], cert, CM)
        self.assertTrue(verified['verified'])
        self.assertIn('epsilon=min(tau,N^-gamma)', verified['domain'])
        self.assertFalse(cert['uniform_full_source_bound_proved'])
        attempt = S.closure_attempt(u, atoms, row, order)
        self.assertEqual(attempt['status'], 'OPEN_SOURCE_FORCING')
        self.assertFalse(attempt['literal_self_state_recurrence'])
        self.assertEqual(len(attempt['unpaid_lower_states']), 2)
        self.assertTrue(all(not l['integer_middle_certificate_inherited'] for l in attempt['unpaid_lower_states']))

    def test_lower_scale_and_zero_source_cannot_inherit_current_bounds(self):
        req = {'universe': [2], 'atoms': [{'primes': [2], 'divisor': 2, 'attenuation': 2}], 'coefficients': ['1']}
        with self.assertRaises(ValueError): S.order_certificate(req, SM)
        req['atoms'][0]['divisor'] = 1; req['coefficients'] = ['0']
        zero = S.order_certificate(req, SM)
        self.assertTrue(zero['zero_source'])
        with self.assertRaises(ValueError): S.endpoint_program(req, zero, '1/5', '1')

    def test_canonical_and_fractional_grid(self):
        self.assertEqual(S.canonical({2: Q(-2, 3), 4: Q(4, 9)}, SM), ((2, 3), (4, -2)))
        grid = S.parameter_grid(64)
        self.assertIn(Q(11, 60), grid)
        gamma = S.select_endpoint_gamma({'order': 3, 'zero_source': False}, '3/11', grid, SM)
        self.assertEqual(gamma, '11/60')
        with self.assertRaises(ValueError): S.parameter_grid(129)


if __name__ == '__main__': unittest.main()
