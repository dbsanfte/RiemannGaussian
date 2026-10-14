"""Focused043 exact semantics; no candidate performance observations."""
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import time
import unittest

import floor_residual_search_043 as S


def basis(n, x):
    return Q(0) if x > 1 else Q((1/x).__floor__(), n)-(1/(n*x)).__floor__()


def residual(p, x):
    if x > 1:
        return Q(0)
    return 1-sum(Q(r['value'])*basis(r['n'], x) for r in p['coefficients'])-sum(
        Q(r['value']) for r in p['steps'] if x <= Q(1, r['q']))


class RecipeTests(unittest.TestCase):
    def test_arbitrary_fractional_root_exact_lower_rounding(self):
        for base in (Q(0), Q(1), Q(2, 7), Q(17, 33)):
            for exponent in ('1/5', '2/7', '3/11', '123/257', '7/2'):
                y = S.root_floor(base, exponent, 9)
                u, v = Q(exponent).numerator, Q(exponent).denominator
                self.assertLessEqual(y**v, base**u)
                self.assertGreater((y+Q(1, 512))**v, base**u)
                self.assertEqual((y*512).denominator, 1)

    def test_root_resource_domain_and_syntax_guards(self):
        for base, exp, bits in ((Q(-1), '1/3', 8), (Q(2), '1/3', 8), (Q(1, 2), '0', 8),
                                (Q(1, 2), '2/4', 8), (Q(1, 2), '1/3', True)):
            with self.assertRaises(ValueError):
                S.root_floor(base, exp, bits)
        with self.assertRaises(OverflowError):
            S.root_floor(Q(1, 2), '1/1000000', 8)

    def test_integer_channel_sieve_against_factorization(self):
        channels = S.arithmetic_channels(64)
        def factor(n):
            exponents = []
            p = 2
            while p <= n:
                e = 0
                while n % p == 0:
                    n //= p
                    e += 1
                if e:
                    exponents.append(e)
                p += 1
            return exponents
        for n in range(1, 65):
            es = factor(n)
            self.assertEqual(channels['mu'][n], 0 if any(e > 1 for e in es) else (-1)**len(es))
            self.assertEqual(channels['liouville'][n], (-1)**sum(es))
            self.assertEqual(channels['radical_sign'][n], (-1)**len(es))
            product = 1
            for e in es:
                product *= -2 if e == 1 else 1 if e == 2 else 0
            self.assertEqual(channels['mu_convolution_mu'][n], product)

    def test_exact_dilation_and_forcing_including_step_boundary(self):
        parent = S.program('toy_parent', {2: Q(-2, 3), 5: Q(7, 11)})
        child = S.program('toy_child', {3: Q(5, 4), 7: Q(-3, 8)})
        for q in (2, 3, 7):
            lift = S.program('lift', S.lift_coefficients(parent, q))
            for x in [Q(2, 2*k+1) for k in range(1, 64)]+[Q(1, q)]:
                self.assertEqual(sum(Q(r['value'])*basis(r['n'], x) for r in lift['coefficients']),
                                 sum(Q(r['value'])*basis(r['n'], q*x) for r in parent['coefficients']))
                for b in ('-1', '-1/2', '0', '1/2', '1'):
                    h = S.forcing_program(parent, child, q, b)
                    self.assertEqual(residual(child, x), Q(b)*residual(parent, q*x)+residual(h, x))

    def test_anchor_and_exact_arbitrary_root_recipe(self):
        recipe = dict(id='toy', channel='mu_minus_half_liouville', taper=dict(alpha='3/11', gamma='123/257'),
                      decay='1/13', anchor_cell_one=True)
        compiler = S.Compiler(8)
        p = compiler.compile(recipe, 8)
        self.assertEqual(p['steps'], [])
        self.assertEqual(sum(Q(r['value'])/r['n'] for r in p['coefficients']), 1)
        self.assertTrue(all(r['n'] < 8 for r in p['coefficients']))
        self.assertEqual(p, compiler.compile(recipe, 8))
        with self.assertRaises(ValueError):
            compiler.compile(recipe, 9)

    def test_strict_contraction_and_zero_boundary(self):
        self.assertFalse(S.contraction_admissible(4, '1', '1/4'))
        self.assertTrue(S.contraction_admissible(4, '1', '1/5'))
        self.assertTrue(S.contraction_admissible(2, '-1', '1/16'))
        self.assertFalse(S.contraction_admissible(2, '1', '1/4'))
        self.assertFalse(S.contraction_admissible(2, '0', '1'))
        self.assertTrue(S.contraction_admissible(2, '0', '1/2'))

    def test_global_training_gram_prices_signed_toy_program(self):
        H = 64
        p = S.program('signed_toy', {2: Q(-3, 7), 5: Q(8, 11)}, {3: Q(1, 2)})
        direct = sum(residual(p, Q(2, 2*k+1))**2/Q(k*(k+1)) for k in range(1, H+1))
        row = S.TrainingNorms(6, H).norm(p)
        self.assertAlmostEqual(row['head_estimate'], float(direct), places=13)
        self.assertGreaterEqual(row['ranking_upper_proxy'], float(direct))
        self.assertFalse(row['rigorous_norm_certificate'])
        # Covers every residue in the periodic tail of this finite toy input.
        M2 = S.tail_bound(p, H)*(H+1)
        for k in range(H+1, H+31):
            self.assertLessEqual(residual(p, Q(2, 2*k+1))**2, M2)

    def test_selection_is_closed_to_final_data_and_no_expected_winner(self):
        recipe = dict(id='anonymous', channel='one', taper=None, decay='0', anchor_cell_one=False)
        assessments = []
        for q in S.MULTIPLIERS:
            for b in S.B_VALUES:
                assessments.append(dict(family='anonymous', q=q, b=b,
                    finite_contraction_tau=None, worst_forcing_power=0, worst_target_power=0,
                    finite_log_bound=None, worst_forcing_log_power=0, worst_target_log_power=0,
                    observations=[dict(N=N, forcing=dict(ranking_upper_proxy=1.)) for N in S.TRAIN_PARENTS]))
        selected = S.select(assessments, [recipe], S.TRAIN_PARENTS)
        self.assertEqual(len(selected), 3)
        with self.assertRaises(ValueError):
            S.select(assessments, [recipe], S.FINAL_PARENTS)
        altered = deepcopy(assessments)
        altered[0]['observations'][-1]['N'] = 80
        with self.assertRaises(ValueError):
            S.select(altered, [recipe], S.TRAIN_PARENTS)
        with self.assertRaises(ValueError):
            S.select(assessments+assessments[:1], [recipe], S.TRAIN_PARENTS)

    def test_log_rate_coordinates_and_impossible_contraction_not_ranked(self):
        import math
        sizes = (8, 16, 24)
        values = [(1+math.log(n))**(-0.7) for n in sizes]
        self.assertAlmostEqual(S.worst_log_power(values, sizes), -0.7, places=12)
        g = S.grammar()
        self.assertTrue(all(0 < Q(e) <= 1 for e in g['log_etas']))
        self.assertIn('negative calibration', g['geometric_contraction_role'])
        self.assertEqual(g['raw_family_count'], 434)
        self.assertEqual(g['refinement_count'], 4340)


if __name__ == '__main__':
    started = time.monotonic()
    result = unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(RecipeTests))
    record = dict(returncode=0 if result.wasSuccessful() else 1, tests=result.testsRun,
                  failures=len(result.failures), errors=len(result.errors), elapsed_seconds=time.monotonic()-started,
                  exposure='synthetic rational floor programs; arithmetic sieve values<=64; one exact syntax fixture; no recipe scores')
    path = Path(__file__).with_name('floor_residual_search_043_development.json')
    receipt = json.loads(path.read_text()) if path.exists() else dict(schema='owned-development-v1', invocations=[])
    receipt['invocations'].append(record)
    path.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(record))
    raise SystemExit(record['returncode'])
