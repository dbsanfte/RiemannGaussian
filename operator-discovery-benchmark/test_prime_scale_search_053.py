from copy import deepcopy
from fractions import Fraction as Q
import unittest
import prime_scale_search_053 as S
import prime_scale_source_053 as P

M, PM = S.Meter(), P.Meter()


class SearchTests(unittest.TestCase):
    def spec(self):
        return {'alphas': ['13/29'], 'scales': [2, 3], 'max_degree': 2, 'coefficient_limit': 3,
                'log_powers': ['0', '1/3'], 'constant_exponents': list(range(-8, 5)), 'max_candidates': 500}

    def test_grammar_integer_mean_annihilation_and_primitivity(self):
        from functools import reduce
        from math import gcd
        bank = S.grammar(self.spec(), M)
        self.assertTrue(bank['words'])
        self.assertFalse(bank['root_locations_restricted'])
        for row in bank['words']:
            self.assertEqual(sum(c*row['q']**j for j, c in enumerate(row['coefficients'])), 0)
            self.assertEqual(reduce(gcd, row['coefficients']), 1)
        self.assertEqual(len(bank['words']), len({(r['alpha'], r['q'], tuple(r['coefficients'])) for r in bank['words']}))

    def test_training_bound_construction_and_scope(self):
        spec = self.spec(); spec['scales'] = [2]; spec['max_degree'] = 1
        source = P.make_source('13/29', 32, meter=PM)
        study = S.search(S.grammar(spec, M), {'13/29': source}, [2, 7, 13], M, PM)
        selected = S.select(study['candidates'], 1)
        self.assertEqual(len(selected['selected']), 1)
        row = selected['selected'][0]
        self.assertEqual(row['request']['bound']['normalization'], 'divide_by_alpha')
        self.assertFalse(row['uniform_arithmetic_bound_proved'])
        self.assertFalse(study['proof_provider_used']); self.assertFalse(study['final_scores_used'])

    def test_exact_interval_sign_and_bound_status(self):
        self.assertEqual(S.assess((Q(-3), Q(-2)), (Q(1), Q(3, 2))), 'FINITE_REFUTATION')
        self.assertEqual(S.assess((Q(-1), Q(1)), (Q(2), Q(3))), 'FINITE_PASS')
        self.assertEqual(S.assess((Q(1), Q(2)), (Q(3, 2), Q(7, 4))), 'UNRESOLVED_INTERVAL')

    def test_cache_key_includes_source_precision(self):
        source = P.make_source('13/29', 12, bits=32, meter=PM)
        other = P.make_source('13/29', 12, bits=36, meter=PM)
        word = {'alpha': '13/29', 'q': 2, 'coefficients': [-2, 1]}
        cache = {}
        S.source_value(source, word, 5, cache, M, PM)
        S.source_value(other, word, 5, cache, M, PM)
        self.assertEqual(len(cache), 4)

    def test_resource_and_rational_domain_guards(self):
        for updates in ({'max_candidates': 1}, {'coefficient_limit': 0}, {'alphas': ['0']},
                        {'scales': [True]}, {'constant_exponents': [1, 0]}):
            spec = self.spec(); spec.update(updates)
            with self.assertRaises((ValueError, OverflowError)): S.grammar(spec, M)


def tearDownModule(): print('SYNTHETIC_WORK operations=%d' % (M.operations+PM.operations))


if __name__ == '__main__': unittest.main()
