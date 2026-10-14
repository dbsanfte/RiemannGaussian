"""Focused044 language tests, synthetic norms and partition guards only."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import floor_residual_search_044 as S


class SearchTests(unittest.TestCase):
    def test_limit_grammar_accepts_new_rationals_rejects_old_fixed_mixture(self):
        recipe = dict(id='toy', base=S.taper('log', '123/257', '5/11'), auxiliary=dict(
            channel='liouville', coefficient='-13/17', envelope=dict(kind='power_amplitude', power='1/263', weight=dict(kind='unit'))))
        proof = S.certify_recipe_limit(recipe)
        self.assertTrue(proof['necessary_condition_only'])
        self.assertFalse(proof['all_scale_upper_bound_proved'])
        with self.assertRaises(ValueError):
            S.weight_limit(dict(kind='fixed_twist', exponent='1/7'))
        with self.assertRaises(ValueError):
            S.envelope_limit(dict(kind='fixed_amplitude', value='1/2', weight=dict(kind='unit')))
        recipe['auxiliary']['envelope']['power'] = '0'
        with self.assertRaises(ValueError):
            S.certify_recipe_limit(recipe)

    def test_log_coordinate_exact_boundaries_and_nonrational_floor(self):
        for n, N, exact in ((2, 16, Q(1, 4)), (6, 36, Q(1, 2)), (4, 64, Q(1, 3)), (17, 17, Q(1))):
            self.assertEqual(S.log_coordinate(n, N, 12), Q((4096*exact).numerator//(4096*exact).denominator, 4096))
        value = S.log_coordinate(3, 17, 10)
        k = int(value*1024)
        self.assertLessEqual(17**k, 3**1024)
        self.assertLess(3**1024, 17**(k+1))

    def test_moving_cutoff_exact_unusual_root_and_resource_guard(self):
        for N, theta in ((100, '3/7'), (64, '1/2'), (31, '19/257')):
            value = S.moving_cutoff(N, theta, S.Meter())
            e = Q(theta)
            self.assertLessEqual(value**e.denominator, N**e.numerator)
            self.assertGreater((value+1)**e.denominator, N**e.numerator)
        with self.assertRaises(OverflowError):
            S.moving_cutoff(31, '1/1000000', S.Meter())

    def test_exact_growing_head_repair_and_signed_auxiliary(self):
        compiler = S.Compiler(37)
        recipe = dict(id='band', base=dict(kind='unit'), auxiliary=dict(channel='liouville', coefficient='1/2',
            envelope=dict(kind='moving_band', cutoff_power='3/7', weight=dict(kind='unit'))))
        p = compiler.compile(recipe, 37)
        c = {r['n']: Q(r['value']) for r in p['coefficients']}
        cutoff = S.moving_cutoff(37, '3/7', compiler.meter)
        for n in range(2, 38):
            expected = -compiler.channels['mu'][n]
            if n > cutoff:
                expected += Q(compiler.channels['liouville'][n], 2)
            self.assertEqual(c.get(n, Q(0)), expected)
        self.assertEqual(p['constant'], '1')
        self.assertFalse(p['steps'])

    def test_vanishing_twist_and_product_are_exactly_rounded(self):
        compiler = S.Compiler(23)
        w = dict(kind='vanishing_twist', rate='2/7', level_power=2)
        values = compiler.weights_at(w, 23)
        bits, beta = 4*22 .bit_length(), Q(2, 7*23 .bit_length()**2)
        for n, value in enumerate(values, 2):
            self.assertLessEqual(value**beta.denominator, Q(1, n)**beta.numerator)
            self.assertGreater((value+Q(1, 1 << bits))**beta.denominator, Q(1, n)**beta.numerator)
        product = dict(kind='product', left=w, right=S.taper('log', '1'))
        self.assertEqual(compiler.weights_at(product, 23),
                         [a*b for a, b in zip(values, compiler.weights_at(product['right'], 23))])

    def test_auxiliary_residual_difference_and_refinement_cells(self):
        p = S.program('p', {2: Q(2, 7), 3: Q(-1, 11)})
        c = S.program('c', {2: Q(3, 5), 6: Q(1, 13)})
        h = S.forcing_program(p, c, 2, '-1/2')
        def cell(v, k):
            return Q(v['constant'])-sum((Q(r['value'])*Q(k % r['n'], r['n']) for r in v['coefficients']), Q(0)) \
                -sum((Q(r['value']) for r in v['steps'] if k >= r['q']), Q(0))
        d = S.difference_program(c, p, 'difference')
        self.assertEqual(d['constant'], '0')
        for k in range(1, 70):
            self.assertEqual(cell(d, k), cell(c, k)-cell(p, k))
            # floor(1/(q*x))=floor(k/q) for almost all of cell k.
            dilated = cell(p, k//2) if k >= 2 else Q(0)
            self.assertEqual(cell(c, k), -Q(1, 2)*dilated+cell(h, k))

    def test_shared_training_norm_matches_synthetic_exact_head(self):
        p = S.program('signed', {2: Q(3, 7), 5: Q(-2, 11)}, {3: Q(-1, 13)}, constant='-1/2')
        price = S.TrainingNorms(7, 128).price([p])[0]
        exact = Q(0)
        for k in range(1, 129):
            value = Q(-1, 2)-Q(3, 7)*Q(k % 2, 2)+Q(2, 11)*Q(k % 5, 5)+(Q(1, 13) if k >= 3 else 0)
            exact += value*value/Q(k*(k+1))
        self.assertAlmostEqual(price['head_estimate'], float(exact), places=13)
        self.assertLessEqual(price['ranking_lower_proxy'], float(exact))
        self.assertFalse(price['rigorous_norm_certificate'])
        self.assertLessEqual(price['tail_upper_proxy'], price['pointwise_tail_proxy'])

    def test_signed_necessity_not_just_negative_cross(self):
        def norm(x):
            return dict(ranking_lower_proxy=x, ranking_upper_proxy=x)
        self.assertTrue(S.cross_diagnostic(norm(1), norm(2), norm(1), 1.5)['signed_needed_proxy'])
        self.assertFalse(S.cross_diagnostic(norm(1), norm(2), norm(1), 10)['signed_needed_proxy'])
        self.assertFalse(S.cross_diagnostic(norm(1), norm(2), norm(1), .5)['signed_needed_proxy'])

    def test_training_partition_and_complete_matrix_guard(self):
        recipes = [dict(id='base'), dict(id='aux')]
        rows = []
        for recipe in recipes:
            for q in S.MULTIPLIERS:
                for b in S.B_VALUES:
                    rows.append(dict(family=recipe['id'], q=q, b=b, has_auxiliary=recipe['id']=='aux',
                        finite_log_bound=dict(A='1', eta='1'), auxiliary_signed_needed_count=0,
                        refinement_signed_needed_count=0, worst_forcing_log_power=-1, worst_target_log_power=-1,
                        observations=[dict(N=N, forcing=dict(ranking_upper_proxy=.1)) for N in S.TRAIN_PARENTS]))
        self.assertEqual(len(S.select(rows, recipes, S.TRAIN_PARENTS)), 4)
        with self.assertRaises(ValueError):
            S.select(rows, recipes, S.FINAL_PARENTS)
        bad = deepcopy(rows)
        bad[0]['observations'][0]['N'] = S.FINAL_PARENTS[0]
        with self.assertRaises(ValueError):
            S.select(bad, recipes, S.TRAIN_PARENTS)
        with self.assertRaises(ValueError):
            S.select(rows[:-1], recipes, S.TRAIN_PARENTS)

    def test_frozen_grammar_all_have_local_proofs_and_no_per_scale_fit(self):
        grammar = S.grammar()
        self.assertEqual(grammar['raw_family_count'], 581)
        self.assertEqual(grammar['refinement_count'], 5810)
        self.assertFalse(grammar['fitted_per_scale_coefficients'])
        for r in grammar['recipes']:
            self.assertTrue(S.certify_recipe_limit(r)['necessary_condition_only'])


if __name__ == '__main__':
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(SearchTests))
    record = dict(returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
                  failures=len(result.failures), errors=len(result.errors), elapsed_seconds=time.monotonic()-started,
                  exposure='typed grammar; small exact coefficient identities; rational synthetic norms128; artificial ranking only')
    path = Path(__file__).with_name('floor_residual_search_044_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1', invocations=[])
    receipt['invocations'].append(record)
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(record))
    raise SystemExit(record['returncode'])
