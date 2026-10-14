"""Independent source and finite-admission regressions; no witness scoring."""
import ast
import copy
from fractions import Fraction as F
from pathlib import Path
import unittest
import cancellation_primitive_state_localizers as A
import cancellation_affine_storage_synthesis as S
import check_cancellation_primitive_state_localizers as I
import test_check_cancellation_affine_storage as T

PROGRAM = dict(target='mu', q=6, C='32', claim='critical')


class PrimitiveStateChecker(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.out = {X: A.build(PROGRAM, X) for X in (1, 2)}
        cls.expected = {X: I.build(PROGRAM, X) for X in (1, 2)}

    def test_no_producer_imports(self):
        source = Path(I.__file__).read_text()
        names = [n.module for n in ast.walk(ast.parse(source)) if isinstance(n, ast.ImportFrom)]
        names += [a.name for n in ast.walk(ast.parse(source)) if isinstance(n, ast.Import) for a in n.names]
        self.assertFalse(any(n and n.startswith('cancellation_') for n in names))
        self.assertIn('check_grouped_arithmetic', names)
        self.assertIn('check_cancellation_affine_storage', names)

    def test_spec_dictionary_and_complete_old_sources(self):
        self.assertEqual(A.SPEC, I.SPEC)
        self.assertEqual(A.descriptors(), I.descriptors())
        ds = I.descriptors()
        self.assertEqual((len(ds['square']), len(ds['relation'])), (366, 613))
        for X, out in self.out.items():
            self.assertTrue(I.check_builder(PROGRAM, X, out)['verified'])
            old = I.B.build(PROGRAM, X)
            self.assertEqual(out['instance']['relation_groups'][:403], old['instance']['relation_groups'])
            self.assertEqual(out['relation_ids'][:403], old['relation_ids'])
            for key in ('square_groups', 'lhs', 'horizon', 'target'):
                self.assertEqual(out['instance'][key], old['instance'][key])
            for key in ('gram_blocks', 'gram_archive', 'storage_blocks', 'gram_specs',
                        'square_ids', 'factor_archive', 'divisor_archive', 'cell_archive'):
                self.assertEqual(out[key], old[key])

    def test_canonical_complete_primitive_domains(self):
        specs = I.primitive_specs(7)
        self.assertEqual(specs['unit'], [dict(kind='unit')])
        self.assertEqual([r['n'] for r in specs['norm']], list(range(1, 8)))
        self.assertEqual([r['n'] for r in specs['inverse_row']], list(range(2, 8)))
        self.assertEqual([r['n'] for r in specs['squarefree_zero']], [4])
        self.assertEqual(specs['prime_power'], [dict(kind='prime_power', p=2, e=1),
                                              dict(kind='prime_power', p=3, e=1),
                                              dict(kind='prime_power', p=2, e=2),
                                              dict(kind='prime_power', p=5, e=1),
                                              dict(kind='prime_power', p=7, e=1)])
        self.assertEqual(specs['coprime_product'], [dict(kind='coprime_product', a=2, b=3)])
        self.assertEqual([(r['a'], r['b']) for r in specs['gcd_product']],
                         [(a, b) for a in range(1, 8) for b in range(a, 8)])
        self.assertEqual(len(specs['gcd_product']), 28)
        self.assertTrue(all(r['a'] <= r['b'] for r in specs['gcd_product']))

    def test_all_210_polynomials_equal_full_unaggregated_sources(self):
        out = self.out[2]
        sources = {(r['family'], r['t']): r for r in out['primitive_sources']}
        for desc, group, arc in zip(I.additions()['relation'], out['instance']['relation_groups'][403:],
                                    out['primitive_state_archive']):
            f, r, i = desc['primitive_family'], desc['region'], desc['atom_index']
            ts = list(range(2, 4) if r == 'parent' else range(4, 8))
            direct = {}
            for t, state in zip(ts, out['gram_blocks']['full_'+r]):
                R = {}
                for spec in I.primitive_specs(t)[f]:
                    R = I.P.add(R, I.G.relation(spec, 'mu', 7))
                direct = I.P.add(direct, I.P.multiply(I.P.parse(state[i], 7), R))
                self.assertEqual(sources[f, t]['primitive_specs'], I.primitive_specs(t)[f])
            aggregate = {}
            for row in group:
                aggregate = I.P.add(aggregate, I.P.multiply(I.P.parse(row['multiplier'], 7),
                                                          I.G.relation(row['spec'], 'mu', 7)))
            self.assertEqual(direct, aggregate)
            self.assertEqual(I.digest(I.P.canonical(direct)), arc['polynomial_sha256'])
            self.assertEqual(direct.get((), F(0)), F(arc['formal_relation_scalar']))
            self.assertEqual(arc['scales'], ts)
        self.assertEqual({d['atom_index'] for d in I.additions()['relation']}, set(range(15)))

    def test_boundary_empty_groups_and_actual_prime_power(self):
        out = self.out[1]
        sources = {(r['family'], r['t']): r for r in out['primitive_sources']}
        self.assertEqual(sources['inverse_row', 1]['primitive_specs'], [])
        self.assertEqual(sources['gcd_product', 1]['source_count'], 1)
        self.assertEqual(sources['norm', 1]['formal_relation_constant'], '-1')
        for desc, group in zip(I.additions()['relation'], out['instance']['relation_groups'][403:]):
            if desc['primitive_family'] in ('coprime_product', 'squarefree_zero'):
                self.assertEqual(group, [])
        row = next(r for r in self.out[2]['primitive_sources'] if r['family'] == 'prime_power' and r['t'] == 4)
        self.assertIn(dict(kind='prime_power', p=2, e=2), row['primitive_specs'])
        self.assertEqual(row['formal_relation_constant'], '2')

    def test_tamper_source_witness_multiplier_and_archive(self):
        for kind in ('source_omit', 'factor', 'state_column', 'state_row', 'new_group',
                     'archive_count', 'archive_hash', 'old_group', 'transport'):
            bad = copy.deepcopy(self.out[2])
            if kind == 'source_omit': bad['primitive_sources'][1]['primitive_specs'].pop()
            elif kind == 'factor':
                row = next(r for r in bad['primitive_sources'] if r['family'] == 'norm' and r['t'] == 4)
                row['primitive_specs'][-1]['factors'] = [[4, 1]]
            elif kind == 'state_column': bad['gram_blocks']['full_child'][0][14] = []
            elif kind == 'state_row': bad['multiplier_sources'].pop()
            elif kind == 'new_group': bad['instance']['relation_groups'][403].pop()
            elif kind == 'archive_count': bad['primitive_state_archive'][0]['source_count'] -= 1
            elif kind == 'archive_hash': bad['primitive_state_archive'][0]['polynomial_sha256'] = '0'*64
            elif kind == 'old_group': bad['instance']['relation_groups'][0].pop()
            else: bad['storage_blocks']['parent_multiplier'] = '-1'
            with self.assertRaises(ValueError, msg=kind): I.check_builder(PROGRAM, 2, bad)
        for spec in (dict(kind='prime_power', p=4, e=1),
                     dict(kind='norm', n=4, factors=[[4, 1]]),
                     dict(kind='gcd_product', a=4, b=4, factors_a=[[2, 1]], factors_b=[[2, 2]])):
            with self.assertRaises(ValueError): I.G.relation(spec, 'mu', 7)

    def test_auxiliary_keeps_all_empty_positions_and_gamma(self):
        out = I.auxiliary()
        self.assertEqual(out, A.auxiliary())
        self.assertEqual(out['instance']['relation_groups'][-210:], [[]]*210)
        self.assertEqual(out['gamma_coefficients'][-210:], ['0']*210)
        self.assertEqual(out['gram_blocks'], {g: [] for g in ('full_parent', 'full_child')})
        self.assertEqual(out['storage_blocks']['parent'], [])
        self.assertEqual(out['storage_blocks']['child'], [])

    def test_full_formal_scalar_ledger_and_nonconstant_separation(self):
        out = self.out[2]
        grams = {g: T.zero() for g in I.gram_specs()}
        grams['storage_K'][0][0] = '1'
        sw = ['0']*366
        rw = ['0']*403+[str((i%5)-2) for i in range(210)]
        weights = dict(square_weights=sw, relation_weights=rw)
        ledger = I.extract_scalar_budget(out['instance'], weights, grams, 2)
        added = A.scalar_budget(rw[-210:], 2)
        self.assertEqual(ledger['added_relation_scalar_budget']['ledger'], added['ledger'])
        self.assertEqual(ledger['matrix_budget']['storage_contribution'], '-4')
        self.assertEqual(F(ledger['B']), F(added['total'])-4)
        self.assertEqual(len(ledger['scalar_ledger']), 366+613)
        self.assertFalse(ledger['nonconstant_identity_verified'])
        # Zero-weight groups still retain their true formal scalar in the ledger.
        unit_parent = ledger['scalar_ledger'][366+403]
        self.assertEqual(unit_parent['formal_scalar'], '-2')
        bad = A.build_additions(2)
        bad['archive'][0]['formal_relation_scalar'] = '999'
        with self.assertRaises(ValueError): I.scalar_budget(rw[-210:], 2, additions_data=bad)
        with self.assertRaises(ValueError): I.extract_scalar_budget(out['instance'], {**weights, 'relation_weights': rw[:-1]}, grams, 2)

    def fixture(self, dual=False):
        instances, blocks, storage, result = T.toy(dual=dual)
        group = [dict(spec=dict(kind='unit'), multiplier=[dict(m=[], c='1')])]
        instances[0]['relation_groups'] = [group]+[[] for _ in range(209)]
        result['source_hashes'] = list(map(I.digest, instances))
        result['grammar_hash'] = I.digest(I.SPEC)
        if dual:
            system = I.coefficient_system(instances, blocks, storage)
            y = {m: F(m == (0, (1, 1))) for m in system['domain']}
            dots = [sum((q*y[m] for m, q in p.items()), F(0)) for p in system['columns']]
            result.update(monomials=[dict(instance=k, m=list(m)) for k, m in system['domain']],
                          weights=[str(y[m]) for m in system['domain']],
                          columns_dot_y=list(map(str, dots[:system['offset']])),
                          gram_columns_dot_y=list(map(str, dots[system['offset']:])))
        else:
            relation = I.G.relation(dict(kind='unit'), 'mu', 1)
            instances[0]['lhs'] = I.P.canonical(I.P.add(I.P.parse(instances[0]['lhs'], 1), relation, F(3)))
            result['source_hashes'] = list(map(I.digest, instances))
            result['weights']['relation_weights'] = ['3']+['0']*209
            result['certificates'] = [S.instantiate_certificate(instances[0], result['weights'], result['grams'], blocks[0], storage[0])]
            upper = [result['grams'][g][i][j] for g in sorted(I.gram_specs()) for i in range(15) for j in range(i, 15)]
            result['exact_column_weights'] = ['1']+['3', '0']+['0', '0']*209+['0']+upper
        return instances, blocks, storage, result

    def test_finite_primal_replays_signed_localizer_and_typed_storage(self):
        inst, blocks, storage, result = self.fixture()
        checked = I.verify_primal(inst, blocks, storage, I.gram_specs(), result)
        self.assertTrue(checked['verified'])
        self.assertFalse(checked['RH_proved'])
        result['grammar_hash'] = I.digest(I.B.SPEC)
        with self.assertRaises(ValueError): I.verify_primal(inst, blocks, storage, I.gram_specs(), result)

    def test_signed_dual_requires_zero_and_missing_coordinates_reject(self):
        inst, blocks, storage, result = self.fixture(dual=True)
        self.assertTrue(I.verify_dual(inst, blocks, storage, I.gram_specs(), result)['verified'])
        inst[0]['relation_groups'][0][0]['multiplier'] = [dict(m=[1], c='1')]
        result['source_hashes'] = list(map(I.digest, inst))
        with self.assertRaisesRegex(ValueError, 'scalar separator signs'):
            I.verify_dual(inst, blocks, storage, I.gram_specs(), result)
        inst[0]['relation_groups'][0][0]['multiplier'] = [dict(m=[1, 1], c='1')]
        result['source_hashes'] = list(map(I.digest, inst))
        with self.assertRaisesRegex(ValueError, 'complete anchored dual coefficient domain'):
            I.verify_dual(inst, blocks, storage, I.gram_specs(), result)

    def test_resource_limits_are_strict(self):
        for kw in (dict(max_horizon=True), dict(max_operations=0), dict(max_terms=False)):
            with self.assertRaises(ValueError): I.build_additions(1, **kw)
        for kw in (dict(max_horizon=2), dict(max_operations=1), dict(max_terms=1), dict(max_coefficient_bits=1)):
            with self.assertRaises(OverflowError): I.build_additions(2, **kw)


if __name__ == '__main__':
    unittest.main()
