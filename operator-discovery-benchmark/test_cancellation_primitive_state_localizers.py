import copy
import unittest
from fractions import Fraction as F
from math import gcd

import cancellation_affine_storage as BASE
import cancellation_affine_storage_synthesis as SYNTH
import cancellation_primitive_state_localizers as P
import cancellation_cubic_gate as GATE
import grouped_arithmetic_language as L


PROGRAM = dict(target='mu', q=6, C='32', claim='critical')


def group_polynomial(group, H):
    out = {}
    for term in group:
        product = L.mul(L.load_poly(term['multiplier']), L.relation(term['spec'], 'mu', H))
        out = L.add(out, product)
    return out


class PrimitiveStateLocalizerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.small = P.build_additions(1)
        cls.medium = P.build_additions(2)

    def test_complete_fixed_dictionary_and_old_program_preserved(self):
        ds, extra = P.descriptors(), P.additions()
        self.assertEqual((len(ds['square']), len(ds['relation'])), (366, 613))
        self.assertEqual(extra['square'], [])
        self.assertEqual(len(extra['relation']), 210)
        self.assertEqual(len({d['id'] for d in extra['relation']}), 210)
        self.assertEqual([(d['primitive_family'], d['region'], d['atom_index'])
                          for d in extra['relation']],
                         [(family, region, i) for family in P.SPEC['primitive_families']
                          for region in ('parent', 'child') for i in range(15)])
        old, new = BASE.build(PROGRAM, 1), P.build(PROGRAM, 1)
        self.assertEqual(old['instance']['lhs'], new['instance']['lhs'])
        self.assertEqual(old['instance']['square_groups'], new['instance']['square_groups'])
        self.assertEqual(old['instance']['relation_groups'], new['instance']['relation_groups'][:403])
        for key in ('square_ids', 'gram_blocks', 'gram_archive', 'storage_blocks', 'gram_specs',
                    'cell_archive', 'divisor_archive', 'factor_archive'):
            self.assertEqual(old[key], new[key])
        self.assertEqual(new['relation_ids'][:403], old['relation_ids'])
        self.assertEqual(new['gram_program'], P.SPEC)
        self.assertEqual(new['dictionary_sha256'], P.digest(ds))

    def test_primitive_domains_complete_order_and_factor_witnesses(self):
        sources = {(r['family'], r['t']): r for r in self.medium['primitive_sources']}
        self.assertEqual(len(sources), 6 * 7)
        for t in range(2, 8):
            norm = sources['norm', t]['primitive_specs']
            self.assertEqual([s['n'] for s in norm], list(range(1, t + 1)))
            for spec in norm:
                self.assertEqual(spec['factors'], L.factor_witness(spec['n']))
            self.assertEqual(sources['unit', t]['primitive_specs'], [dict(kind='unit')])
            self.assertEqual(sources['inverse_row', t]['primitive_specs'],
                             [dict(kind='inverse_row', n=n) for n in range(2, t + 1)])
            self.assertEqual(sources['squarefree_zero', t]['primitive_specs'],
                             [dict(kind='squarefree_zero', n=4)] if t >= 4 else [])
            coprime = [dict(kind='coprime_product', a=a, b=b)
                       for a in range(2, t + 1) for b in range(a, t + 1)
                       if a * b <= t and gcd(a, b) == 1]
            self.assertEqual(sources['coprime_product', t]['primitive_specs'], coprime)
            gcds = sources['gcd_product', t]['primitive_specs']
            self.assertEqual([(s['a'], s['b']) for s in gcds],
                             [(a, b) for a in range(1, t + 1) for b in range(a, t + 1)])
            for family in P.SPEC['primitive_families']:
                source = sources[family, t]
                self.assertEqual(source['source_count'], len(source['primitive_specs']))
                self.assertEqual(source['source_sha256'], P.digest(source['primitive_specs']))
                self.assertTrue(source['complete_source'])
        self.assertEqual(sources['prime_power', 7]['primitive_specs'],
                         [dict(kind='prime_power', p=p, e=e)
                          for p, e in [(2, 1), (3, 1), (2, 2), (5, 1), (7, 1)]])

    def test_all_groups_reconstruct_complete_unaggregated_sources(self):
        # Coefficient equality across all atoms checks state multiplication and
        # aggregation, including cubic/quartic divisor-cell state products.
        sources = {(r['family'], r['t']): r for r in self.small['primitive_sources']}
        blocks = BASE.build_blocks(1)['blocks']
        for desc, group, archive in zip(P.additions()['relation'], self.small['relation_groups'],
                                        self.small['archive']):
            family, region, i = desc['primitive_family'], desc['region'], desc['atom_index']
            expected, by_spec = {}, {}
            for t, row in zip(archive['scales'], blocks['full_' + region]):
                state = L.load_poly(row[i])
                for spec in sources[family, t]['primitive_specs']:
                    expected = L.add(expected, L.mul(state, L.relation(spec, 'mu', 3)))
                    key = P.digest(spec)
                    by_spec[key] = L.add(by_spec.get(key, {}), state)
            self.assertEqual(group_polynomial(group, 3), expected)
            self.assertEqual(archive['polynomial_sha256'], P.digest(L.dump_poly(expected)))
            self.assertEqual(archive['relation_group_sha256'], P.digest(group))
            self.assertEqual(len(group), len(by_spec))
            for term in group:
                self.assertEqual(L.load_poly(term['multiplier']), by_spec[P.digest(term['spec'])])
            # Replay a genuine native primitive certificate for every group.
            cert = dict(target='mu', horizon=3, lhs=L.dump_poly(expected), squares=[], relations=group)
            self.assertTrue(L.compile_certificate(cert)['finite_identity_verified'])

    def test_formal_constants_and_zero_sources_retained(self):
        sources = {(r['family'], r['t']): r for r in self.medium['primitive_sources']}
        self.assertEqual([sources['norm', t]['formal_relation_constant'] for t in range(2, 8)],
                         ['-2', '-3', '-3', '-4', '-5', '-6'])
        self.assertEqual([sources['prime_power', t]['formal_relation_constant'] for t in range(2, 8)],
                         ['1', '2', '2', '3', '3', '4'])
        z = list(map(F, P.SPEC['formal_state_vector']))
        for desc, row in zip(P.additions()['relation'], self.medium['archive']):
            expected = z[desc['atom_index']] * sum(
                F(sources[desc['primitive_family'], t]['formal_relation_constant'])
                for t in row['scales'])
            self.assertEqual(F(row['formal_relation_scalar']), expected)
        weights = ['0'] * 210
        weights[30] = '-2'  # norm, parent, unit
        budget = P.scalar_budget(weights, 2, additions_data=self.medium)
        self.assertEqual(budget['total'], '10')
        self.assertEqual(len(budget['ledger']), 210)
        empty = [i for i, d in enumerate(P.additions()['relation'])
                 if d['primitive_family'] in ('squarefree_zero', 'coprime_product')]
        for i in empty:
            self.assertEqual(self.small['relation_groups'][i], [])
            self.assertEqual(self.small['archive'][i]['source_count'], 0)
            self.assertEqual(self.small['archive'][i]['relation_group_sha256'], P.digest([]))
            self.assertEqual(self.small['archive'][i]['polynomial_sha256'], P.digest([]))
        # Actual zero multipliers/spec relations also remain in native groups.
        self.assertTrue(any(t['multiplier'] == [] for g in self.small['relation_groups'] for t in g))
        self.assertTrue(any(t['spec'] == dict(kind='gcd_product', a=1, b=1,
                                            factors_a=[], factors_b=[])
                            for g in self.small['relation_groups'] for t in g))

    def test_auxiliary_extends_only_zero_cubic_columns_and_compiles(self):
        old, new = BASE.auxiliary(), P.auxiliary()
        self.assertEqual(old['instance']['lhs'], new['instance']['lhs'])
        self.assertEqual(old['instance']['square_groups'], new['instance']['square_groups'])
        self.assertEqual(new['instance']['relation_groups'][:403], old['instance']['relation_groups'])
        self.assertEqual(new['instance']['relation_groups'][403:], [[] for _ in range(210)])
        self.assertEqual(new['gamma_coefficients'][:403], old['gamma_coefficients'])
        self.assertEqual(new['gamma_coefficients'][403:], ['0'] * 210)
        self.assertEqual(GATE.build_constraint(P.descriptors())['instance'], new['instance'])
        for key in ('gram_specs', 'gram_blocks', 'storage_blocks'):
            self.assertEqual(new[key], old[key])
        source = P.build(PROGRAM, 1)
        cols, lhs, ms, shape, offset, blocks, specs = SYNTH.prepare(
            [source['instance'], new['instance']], [source['gram_blocks'], new['gram_blocks']],
            [source['storage_blocks'], new['storage_blocks']])
        self.assertEqual(shape, (366, 613))
        self.assertEqual(len(cols) - offset, 360)
        self.assertEqual(specs, BASE.gram_specs())

    def test_strict_limits_canonical_rows_and_no_mutation(self):
        for limits in [dict(max_horizon=2), dict(max_operations=100), dict(max_terms=1),
                       dict(max_coefficient_bits=1)]:
            with self.assertRaises(OverflowError):
                P.build_additions(1, **limits)
        for X in (True, 0, -1, 1.0):
            with self.assertRaises(ValueError):
                P.build_additions(X)
        blocks = BASE.build_blocks(1)['blocks']
        saved = copy.deepcopy(blocks)
        P.build_additions(1, blocks=blocks)
        self.assertEqual(blocks, saved)
        blocks['full_child'][0][1] = []
        with self.assertRaises(ValueError):
            P.build_additions(1, blocks=blocks)
        with self.assertRaises(ValueError):
            P.build(dict(PROGRAM, target='c'), 1)
        with self.assertRaises(ValueError):
            P.scalar_budget([0.0] * 210, 1)
        with self.assertRaises(OverflowError):
            P.build(dict(PROGRAM, C=str(2 ** 33)), 1, max_coefficient_bits=32)
        with self.assertRaises(ValueError):
            P.scalar_budget(['0'] * 210, 2, additions_data=self.small)


if __name__ == '__main__':
    unittest.main()
