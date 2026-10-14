"""Synthetic arithmetic and hostile-certificate tests; no scientific data."""
import copy
from fractions import Fraction
from math import prod
import random
import unittest

from check_mobius_divisor_correction_070 import GRID, SCHEMA, Meter, verify_correction

METERS = []


def text(q):
    q = Fraction(q)
    return str(q.numerator) if q.denominator == 1 else f'{q.numerator}/{q.denominator}'


def sparse(poly):
    return [{'indices': list(k), 'numerator': v} for k, v in sorted(poly.items()) if v]


def oracle_column(n, multiplier):
    # Build sum of differences from a symbolic prefix table, including M1=1.
    result = {}
    for divisor in range(1, n + 1):
        if n % divisor:
            continue
        for s, sign in ((divisor, 1), (divisor - 1, -1)):
            if s == 0:
                continue
            key = tuple(sorted(multiplier + (() if s == 1 else (s,))))
            result[key] = result.get(key, 0) + sign
    return {k: v for k, v in result.items() if v}


def rounded_weight(weight, sigma):
    sigma = Fraction(sigma)
    target = weight ** sigma.numerator * GRID ** sigma.denominator
    lo, hi = 0, weight * GRID
    while lo < hi:
        middle = (lo + hi) // 2
        if middle ** sigma.denominator >= target:
            hi = middle
        else:
            lo = middle + 1
    return lo


def fixture(poly=None, degree=3, U=6, denominator=3, columns=None,
            lambdas=None, dual=None, box=4, exponents=('0', '1/2', '2/3', '1'), T=None):
    poly = {(): 7, (2,): -3, (2, 2): 4, (2, 3, 5): -2} if poly is None else poly
    columns = [] if columns is None else columns
    lambdas = [] if lambdas is None else lambdas
    dual = {} if dual is None else dual
    T = U if T is None else T
    baseline = {k: GRID * v for k, v in poly.items()}
    def upper(q):
        return Fraction(sum(abs(v) * prod(k) for k, v in q.items()), GRID * denominator)
    cert = {'schema': SCHEMA, 'input': {'degree': degree, 'U': U, 'denominator': denominator, 'polynomial': sparse(poly)}, 'constraint_radius': T, 'coefficient_grid': GRID, 'price_exponents': list(exponents), 'options': {'rounds': 3, 'lp_seconds': 2.0}, 'baseline_unconditional_bound': text(upper(baseline)), 'rounds': [], 'conditional_prefix_bounds_paid': False, 'uniform_head_bound_proved': False, 'RH_proved': False, 'learner_mobius_signs_accessed': False}
    choices = [(upper(baseline), 0, -1, baseline, [])]
    if columns:
        residual = dict(baseline)
        supports = []
        for column, value in zip(columns, lambdas):
            support = oracle_column(column['n'], tuple(column['multiplier_indices']))
            supports.append(support)
            for k, c in support.items():
                residual[k] = residual.get(k, 0) + value * c
        residual = {k: v for k, v in residual.items() if v}
        lower = Fraction(sum(dual.get(k, 0) * v for k, v in poly.items()) - box * sum(abs(sum(dual.get(k, 0) * v for k, v in c.items())) for c in supports), GRID * denominator)
        row = {'columns': columns, 'lambda_numerators': lambdas, 'residual': sparse(residual), 'dual': sparse(dual), 'box': box, 'primal_upper': text(upper(residual)), 'boxed_lower': text(lower), 'gap': text(upper(residual) - lower), 'solver': {'status': 'synthetic'}, 'search': {'policy': None}}
        cert['rounds'] = [row]
        choices.append((upper(residual), sum(bool(v) for v in lambdas), 0, residual, sorted({c['n'] for c, v in zip(columns, lambdas) if v})))
    chosen = min(choices, key=lambda x: x[:3])
    selected_upper, _, index, selected, used = chosen
    cert['selected_round'] = index
    cert['selected_polynomial'] = sparse(selected)
    prices = []
    for sigma in exponents:
        sums = [0] * (degree + 1)
        for k, v in selected.items():
            sums[len(k)] += abs(v) * rounded_weight(prod(k), sigma)
        prices.append({'sigma': sigma, 'coefficients': [text(Fraction(v, GRID ** 2 * denominator)) for v in sums]})
    cert['selected_conditional_prices'] = prices
    cert['used_constraints'] = used
    cert['full_divisor_system_used'] = used == list(range(2, T + 1))
    cert['constant_only_selected'] = not any(selected)
    cert['scalar_fake'] = {'source_value': text(Fraction(poly.get((), 0), denominator)), 'corrected_value': text(Fraction(selected.get((), 0), GRID * denominator)), 'violated_used_constraints': [n for n in used if n % 2], 'actual_mobius_assignment': False}
    return cert


def verify(cert, limit=300_000_000_000):
    meter = Meter(limit=limit)
    METERS.append(meter)
    return verify_correction(cert, meter)


def improving_fixture():
    # G3=1-M2+M3. Subtracting it converts this source to the constant 2.
    return fixture({(): 3, (2,): -1, (3,): 1}, degree=2, U=3,
                   columns=[{'n': 3, 'multiplier_indices': []}], lambdas=[-GRID], dual={(): GRID, (2,): -GRID, (3,): GRID})


class CheckerTests(unittest.TestCase):
    def test_arbitrary_mixed_repeated_and_fractional_prices(self):
        result = verify(fixture())
        self.assertTrue(result['verified'])
        self.assertEqual(result['source_actual_value'], '7/3')
        self.assertFalse(result['original_source_binding_proved'])

    def test_odd_constraint_excludes_fake(self):
        cert = improving_fixture()
        result = verify(cert)
        self.assertEqual(cert['selected_round'], 0)
        self.assertEqual(cert['scalar_fake']['violated_used_constraints'], [3])
        self.assertEqual(result['selected_actual_value'], '2/3')

    def test_squareful_constraint_and_repeated_multiplier(self):
        support = oracle_column(4, (2, 2))
        poly = dict(support)
        poly[()] = 5
        cert = fixture(poly, degree=3, U=4, columns=[{'n': 4, 'multiplier_indices': [2, 2]}], lambdas=[-GRID])
        result = verify(cert)
        self.assertEqual(result['source_actual_value'], '5/3')
        self.assertEqual(cert['scalar_fake']['violated_used_constraints'], [])

    def test_full_domain_and_triangular_constant(self):
        cols = [{'n': n, 'multiplier_indices': []} for n in range(2, 7)]
        poly = {(): 2}
        for c in cols:
            for k, v in oracle_column(c['n'], ()).items():
                poly[k] = poly.get(k, 0) + v
        cert = fixture(poly, degree=2, columns=cols, lambdas=[-GRID] * len(cols))
        self.assertTrue(verify(cert)['verified'])
        self.assertTrue(cert['full_divisor_system_used'])
        self.assertTrue(cert['constant_only_selected'])

    def test_extended_constraint_radius(self):
        cert = fixture({(2,): 3}, degree=2, U=2, T=7, columns=[{'n': 7, 'multiplier_indices': [7]}], lambdas=[0])
        self.assertTrue(verify(cert)['verified'])

    def test_unit_radius_constant_and_empty_polynomial(self):
        for poly in ({(): -13}, {}):
            cert = fixture(poly, degree=8, U=1)
            self.assertTrue(verify(cert)['verified'])
            self.assertTrue(cert['full_divisor_system_used'])

    def test_zero_lambda_column_support_kept(self):
        cert = fixture({(2,): 1}, U=3, columns=[{'n': 3, 'multiplier_indices': [2]}], lambdas=[0], dual={(2, 3): GRID})
        self.assertTrue(verify(cert)['verified'])

    def test_cancelled_support_dual_retained(self):
        cert = improving_fixture()
        self.assertTrue(verify(cert)['verified'])
        self.assertNotIn([2], [t['indices'] for t in cert['rounds'][0]['residual']])
        self.assertIn([2], [t['indices'] for t in cert['rounds'][0]['dual']])

    def test_round_tie_uses_baseline(self):
        cert = fixture({(): 1}, U=3, columns=[{'n': 3, 'multiplier_indices': []}], lambdas=[0])
        self.assertEqual(verify(cert)['selected_upper'], '1/3')
        self.assertEqual(cert['selected_round'], -1)

    def test_round_tie_stable_index(self):
        cert = improving_fixture()
        cert['rounds'].append(copy.deepcopy(cert['rounds'][0]))
        self.assertTrue(verify(cert)['verified'])
        self.assertEqual(cert['selected_round'], 0)

    def test_box_bound_fractional_grid_correction(self):
        cert = fixture({(): 2, (2,): -1, (3,): 1}, degree=2, U=3, columns=[{'n': 3, 'multiplier_indices': []}], lambdas=[-(GRID // 3)], box=1)
        self.assertTrue(verify(cert)['verified'])

    def test_random_arbitrary_polynomials(self):
        rng = random.Random(7092)
        for _ in range(12):
            poly = {}
            for j in range(15):
                key = tuple(sorted(rng.randrange(2, 11) for _ in range(rng.randrange(5))))
                poly[key] = rng.randrange(-20, 21)
            cols = [{'n': 9, 'multiplier_indices': [2, 2]}, {'n': 6, 'multiplier_indices': [3]}]
            cert = fixture({k: v for k, v in poly.items() if v}, degree=4, U=10, columns=cols, lambdas=[rng.randrange(-GRID, GRID), rng.randrange(-GRID, GRID)])
            self.assertTrue(verify(cert)['verified'])

    def test_finite_premise_failure_is_recorded(self):
        result = verify(fixture({(): 2}, U=20, exponents=('0', '1')))
        self.assertEqual(result['finite_C1_prefix_premises'], [False, True])

    def test_degree_eight_powers_are_retained(self):
        cert = fixture({(2,) * 8: -3}, degree=8, U=2)
        self.assertTrue(verify(cert)['verified'])
        self.assertEqual(len(cert['selected_conditional_prices'][0]['coefficients']), 9)
        self.assertNotEqual(cert['selected_conditional_prices'][0]['coefficients'][8], '0')

    def test_limited_meter(self):
        with self.assertRaisesRegex(ValueError, 'work limit'):
            verify(fixture(), limit=2)

    def test_elapsed_time_limit(self):
        with self.assertRaisesRegex(ValueError, 'time limit'):
            verify_correction(fixture(), Meter(seconds=-1))

    def test_integer_power_limit(self):
        cert = fixture({(2,): 1}, U=2)
        cert['price_exponents'] = ['1/100000']
        with self.assertRaisesRegex(ValueError, 'power'):
            verify(cert)

    def test_empty_price_request(self):
        self.assertEqual(verify(fixture(exponents=()))['finite_C1_prefix_premises'], [])

    def test_n_two_unit_substitution(self):
        cert = fixture({(): -4, (2,): 9}, degree=2, U=2, columns=[{'n': 2, 'multiplier_indices': []}], lambdas=[-3 * GRID], box=3)
        self.assertEqual(verify(cert)['source_actual_value'], '-4/3')
        self.assertEqual(cert['scalar_fake']['violated_used_constraints'], [])

    def test_zero_polynomial_nonconstant_flag_vacuous(self):
        cert = fixture({}, degree=2, U=3)
        self.assertEqual(verify(cert)['selected_upper'], '0')
        self.assertTrue(cert['constant_only_selected'])

    def test_high_denominator_rational_weights(self):
        cert = fixture({(3, 3): 1}, degree=2, U=3, exponents=('7/31', '29/31'))
        self.assertTrue(verify(cert)['verified'])

    def test_degree_two_prime_difference(self):
        cert = fixture({(2, 5): -2, (2, 4): 2, (2,): -2}, degree=2, U=5, columns=[{'n': 5, 'multiplier_indices': [2]}], lambdas=[2 * GRID])
        self.assertTrue(verify(cert)['verified'])
        self.assertEqual(cert['selected_polynomial'], [])

    def test_capacity_refuses_prospective_storage(self):
        from check_mobius_divisor_correction_070 import _capacity
        with self.assertRaisesRegex(ValueError, 'memory'):
            _capacity(2_000_000)

    def test_column_discovery_order_need_not_be_sorted(self):
        cert = fixture({(): 1}, U=6, columns=[{'n': 6, 'multiplier_indices': [2]}, {'n': 3, 'multiplier_indices': []}], lambdas=[0, 0])
        self.assertTrue(verify(cert)['verified'])


def corruption(name, mutator, builder=improving_fixture):
    def run(self):
        cert = builder()
        mutator(cert)
        with self.assertRaises(ValueError):
            verify(cert)
    run.__name__ = 'test_reject_' + name
    setattr(CheckerTests, run.__name__, run)


corruption('schema', lambda c: c.update(schema='incorrect'))
corruption('extra_top_key', lambda c: c.update(hidden_source=True))
corruption('missing_input_key', lambda c: c['input'].pop('U'))
corruption('boolean_integer', lambda c: c['input'].update(U=True))
corruption('grid', lambda c: c.update(coefficient_grid=GRID + 1))
corruption('negative_denominator', lambda c: c['input'].update(denominator=-3))
corruption('degree', lambda c: c['input'].update(degree=1))
corruption('radius', lambda c: c.update(constraint_radius=2))
corruption('noncanonical_fraction', lambda c: c.update(baseline_unconditional_bound='6/2'))
corruption('price_exponent_outside_range', lambda c: c.update(price_exponents=['3/2']))
corruption('price_exponent_duplicate', lambda c: c.update(price_exponents=['1/2', '1/2']))
corruption('monomial_order', lambda c: c['input']['polynomial'].reverse())
corruption('duplicate_term', lambda c: c['input']['polynomial'].append(copy.deepcopy(c['input']['polynomial'][-1])))
corruption('zero_term', lambda c: c['input']['polynomial'][0].update(numerator=0))
corruption('source_variable_one', lambda c: c['input']['polynomial'][1].update(indices=[1]))
corruption('source_variable_outside_radius', lambda c: c['input']['polynomial'][1].update(indices=[4]))
corruption('source_coefficient_bit_limit', lambda c: c['input']['polynomial'][0].update(numerator=1 << 4096))
corruption('baseline_bound', lambda c: c.update(baseline_unconditional_bound='0'))
corruption('duplicate_columns', lambda c: (c['rounds'][0]['columns'].append(copy.deepcopy(c['rounds'][0]['columns'][0])), c['rounds'][0]['lambda_numerators'].append(0)))
corruption('lambda_length', lambda c: c['rounds'][0]['lambda_numerators'].append(1))
corruption('lambda_outside_box', lambda c: c['rounds'][0].update(lambda_numerators=[5 * GRID]))
corruption('box_zero', lambda c: c['rounds'][0].update(box=0))
corruption('constraint_n_one', lambda c: c['rounds'][0]['columns'][0].update(n=1))
corruption('constraint_n_outside_radius', lambda c: c['rounds'][0]['columns'][0].update(n=4))
corruption('multiplier_degree', lambda c: c['rounds'][0]['columns'][0].update(multiplier_indices=[2, 2]))
corruption('multiplier_order', lambda c: (c['input'].update(degree=3), c['rounds'][0]['columns'][0].update(multiplier_indices=[3, 2])))
corruption('residual_constant', lambda c: c['rounds'][0]['residual'][0].update(numerator=GRID))
corruption('residual_dropped', lambda c: c['rounds'][0].update(residual=[]))
corruption('dual_outside_union', lambda c: c['rounds'][0]['dual'].append({'indices': [2, 3], 'numerator': 1}))
corruption('dual_feasibility', lambda c: c['rounds'][0]['dual'][0].update(numerator=GRID + 1))
corruption('primal_upper', lambda c: c['rounds'][0].update(primal_upper='0'))
corruption('boxed_lower', lambda c: c['rounds'][0].update(boxed_lower='0'))
corruption('gap', lambda c: c['rounds'][0].update(gap='0'))
corruption('selected_index', lambda c: c.update(selected_round=-1))
corruption('selected_polynomial', lambda c: c.update(selected_polynomial=[]))
corruption('conditional_price', lambda c: c['selected_conditional_prices'][1]['coefficients'].__setitem__(0, '0'))
corruption('conditional_degree_dropped', lambda c: c['selected_conditional_prices'][0]['coefficients'].pop())
corruption('used_constraint', lambda c: c.update(used_constraints=[]))
corruption('full_system_flag', lambda c: c.update(full_divisor_system_used=True))
corruption('constant_flag', lambda c: c.update(constant_only_selected=False))
corruption('fake_source', lambda c: c['scalar_fake'].update(source_value='0'))
corruption('fake_corrected', lambda c: c['scalar_fake'].update(corrected_value='0'))
corruption('fake_violation', lambda c: c['scalar_fake'].update(violated_used_constraints=[]))
corruption('fake_actual_claim', lambda c: c['scalar_fake'].update(actual_mobius_assignment=True))
corruption('conditional_paid', lambda c: c.update(conditional_prefix_bounds_paid=True))
corruption('uniform_claim', lambda c: c.update(uniform_head_bound_proved=True))
corruption('RH_claim', lambda c: c.update(RH_proved=True))
corruption('learner_sign_access', lambda c: c.update(learner_mobius_signs_accessed=True))
corruption('metadata_nonfinite', lambda c: c['options'].update(seconds=float('nan')))
corruption('metadata_non_json', lambda c: c['rounds'][0].update(search={'bad': (1, 2)}))
corruption('metadata_depth', lambda c: c['options'].update(nested=[[[[[[[[[[[[[[[[[[0]]]]]]]]]]]]]]]]]]))
corruption('fake_boolean_constraint', lambda c: c['scalar_fake'].update(violated_used_constraints=[True]))
corruption('used_boolean_constraint', lambda c: c.update(used_constraints=[True]))
corruption('price_noncanonical_coefficient', lambda c: c['selected_conditional_prices'][0]['coefficients'].__setitem__(0, '2/3' if c['selected_conditional_prices'][0]['coefficients'][0] != '2/3' else '4/6'))
corruption('too_many_rounds', lambda c: c.update(rounds=c['rounds'] * 9))

if __name__ == '__main__':
    unittest.main()
