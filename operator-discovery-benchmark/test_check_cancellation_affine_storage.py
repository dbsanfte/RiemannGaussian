"""Independent finite-admission regressions, with no research scoring."""
import ast
import copy
from fractions import Fraction as F
from pathlib import Path
import unittest
import check_cancellation_affine_storage as I
import cancellation_affine_storage as A
import cancellation_affine_storage_synthesis as S


def zero():
    return [['0']*15 for _ in range(15)]


def toy(dual=False, K0=False, cross=False):
    atom = [dict(m=[1], c='1')]
    parent = [[] for _ in range(15)]; parent[0] = [dict(m=[], c='1')]; parent[2] = atom
    child = [[] for _ in range(15)]; child[0] = [dict(m=[], c='1')]; child[2] = [dict(m=[1], c='3')]
    if cross:
        parent[1] = copy.deepcopy(parent[2]); child[1] = copy.deepcopy(child[2])
    blocks = [dict(full_child=[child], full_parent=[parent])]
    storage = [I.storage_transport(blocks[0])]
    lhs = [dict(m=[1, 1], c='-1')] if dual else [dict(m=[], c='1')]+([] if K0 else [dict(m=[1, 1], c='5')])
    instances = [dict(target='mu', horizon=1, lhs=lhs,
                      square_groups=[] if dual else [[dict(weight='1', poly=[dict(m=[], c='1')])]], relation_groups=[])]
    grams = {g: zero() for g in I.gram_specs()}
    if not K0:
        grams['storage_K'][2][2] = '1'
    result = dict(status='finite_PSD_certificate', gram_specs=I.gram_specs(), grams=grams,
                  source_hashes=list(map(I.I.digest, instances)), gram_block_hashes=list(map(I.I.digest, blocks)),
                  storage_block_hashes=list(map(I.I.digest, storage)), weights=dict(square_weights=['1'], relation_weights=[]),
                  constant_slacks=['0'], global_bound_proved=False, RH_proved=False)
    if dual:
        system = I.coefficient_system(instances, blocks, storage)
        y = {m: F(m == (0, (1, 1))) for m in system['domain']}
        dots = [sum((q*y[m] for m, q in p.items()), F(0)) for p in system['columns']]
        matrices = {}
        for group in I.gram_specs():
            matrix = zero()
            for i in range(15):
                for j in range(i, 15):
                    value = sum((q*y[0, m] for m, q in system['cross'][group, i, j, 0].items()), F(0))
                    matrix[i][j] = matrix[j][i] = str(value)
            matrices[group] = dict(matrix=matrix)
        result.update(status='exact_separator', certified=True,
                      monomials=[dict(instance=k, m=list(m)) for k, m in system['domain']],
                      weights=[str(y[m]) for m in system['domain']], lhs_dot_y='-1',
                      columns_dot_y=list(map(str, dots[:system['offset']])),
                      gram_columns_dot_y=list(map(str, dots[system['offset']:])), gram_duals=matrices,
                      constant_coordinates=['0'], all_C_q_extension_requires_zero_constant_coordinates=True)
        result.pop('grams'); result.pop('constant_slacks')
    else:
        # Producer creates proposals; admission uses independent algebra.
        result['certificates'] = [S.instantiate_certificate(instances[0], result['weights'], grams, blocks[0], storage[0])]
        upper = [grams[g][i][j] for g in sorted(I.gram_specs()) for i in range(15) for j in range(i, 15)]
        result['exact_column_weights'] = ['1', '0']+upper
    return instances, blocks, storage, result


class AffineChecker(unittest.TestCase):
    def check(self, fixture, dual=False):
        instances, blocks, storage, result = fixture
        return (I.verify_dual if dual else I.verify_primal)(instances, blocks, storage, I.gram_specs(), result)

    def test_no_producer_imports(self):
        source = Path(I.__file__).read_text()
        imports = [node.module for node in ast.walk(ast.parse(source)) if isinstance(node, ast.ImportFrom)]
        imports += [name.name for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Import) for name in node.names]
        self.assertFalse(any(name and name.startswith('cancellation_affine') for name in imports))
        self.assertIn('check_cancellation_complete_gram_program', imports)

    def test_independent_full_source_and_auxiliary(self):
        program = dict(target='mu', q=6, C='32', claim='critical')
        self.assertEqual(I.SPEC, A.SPEC)
        for X in (1, 2):
            out = A.build(program, X)
            self.assertTrue(I.check_builder(program, X, out)['verified'])
            base = I.B.build(program, X)
            for key in ('instance', 'dictionary_sha256', 'square_ids', 'relation_ids', 'cell_archive'):
                self.assertEqual(out[key], base[key])
            bad = copy.deepcopy(out); bad['storage_blocks']['parent'].pop()
            with self.assertRaises(ValueError):
                I.check_builder(program, X, bad)
            bad = copy.deepcopy(out); bad['instance']['square_groups'].pop()
            with self.assertRaises(ValueError):
                I.check_builder(program, X, bad)
            bad = copy.deepcopy(out); bad['instance']['relation_groups'].pop()
            with self.assertRaises(ValueError):
                I.check_builder(program, X, bad)
            bad = copy.deepcopy(out); bad['gram_blocks']['full_child'][0][6] = []
            with self.assertRaises(ValueError):
                I.check_builder(program, X, bad)
        self.assertEqual(I.auxiliary(), A.auxiliary())
        self.assertEqual(I.auxiliary()['storage_blocks']['parent'], [])

    def test_exact_compiler_domain_columns(self):
        program = dict(target='mu', q=6, C='32', claim='critical')
        built = [I.build(program, 1), I.auxiliary()]
        instances = [row['instance'] for row in built]
        blocks = [row['gram_blocks'] for row in built]
        storage = [row['storage_blocks'] for row in built]
        cols, lhs, domain, shape, offset, _, specs = S.prepare(instances, blocks, storage)
        independent = I.coefficient_system(instances, blocks, storage, specs)
        def unflatten(poly):
            return {(m[0], tuple(m[1:])): q for m, q in poly.items()}
        self.assertEqual(independent['domain'], [(m[0], tuple(m[1:])) for m in domain])
        self.assertEqual(independent['lhs'], unflatten(lhs))
        self.assertEqual(independent['columns'], list(map(unflatten, cols)))
        self.assertEqual(independent['offset'], offset)
        self.assertEqual(independent['shape'][:2], tuple(shape))
        self.assertEqual(len(cols)-offset, 360)

    def test_nonzero_K_toy_and_K0_embedding(self):
        for K0 in (False, True):
            result = self.check(toy(K0=K0))
            self.assertTrue(result['coercivity_verified'])
            self.assertTrue(result['signed_increment_identity_verified'])
            self.assertFalse(result['storage_is_nonnegative_SOS'])

    def test_wrong_sign_and_factor_and_source_omission(self):
        for edit in ('factor', 'orientation', 'parent_source', 'child_source'):
            fixture = copy.deepcopy(toy()); storage = fixture[2][0]
            if edit == 'factor': storage['parent_multiplier'] = '-1'
            elif edit == 'orientation': storage['child_multiplier'] = '-1'
            elif edit == 'parent_source': storage['parent'] = []
            else: storage['child'][0][2] = []
            fixture[3]['storage_block_hashes'] = list(map(I.I.digest, fixture[2]))
            with self.assertRaises(ValueError):
                self.check(fixture)

    def test_wrong_K_and_target_rearrangement(self):
        for edit in ('K', 'increment', 'transformed', 'original', 'negative_parent_SOS'):
            fixture = copy.deepcopy(toy()); record = fixture[3]['certificates'][0]
            if edit == 'K': record['storage_proof']['K'][2][2] = '2'
            elif edit == 'increment': record['storage_proof']['polynomial'] = []
            elif edit == 'transformed': record['transformed_lhs'] = fixture[0][0]['lhs']
            elif edit == 'original': record['original_lhs'] = []
            else:
                record['transformed_target_certificate']['squares'].append(dict(weight='-4', poly=[dict(m=[1], c='1')]))
            with self.assertRaises(ValueError):
                self.check(fixture)

    def test_nonPSD_coercivity_even_when_R_PSD(self):
        K = zero(); K[1][1] = '-1/2'
        R = zero(); R[1][1] = '1/2'
        self.assertTrue(I.I.verify_psd(R)['PSD_verified'])
        with self.assertRaises(ValueError):
            I.anchored_matrix(K)
        fixture = copy.deepcopy(toy()); fixture[3]['grams']['storage_K'] = K
        with self.assertRaises(ValueError):
            self.check(fixture)

    def test_all_cross_constants_and_initial_cost(self):
        grams = {g: zero() for g in I.gram_specs()}
        K = grams['storage_K']
        for i in (6, 7):
            for j in (6, 7): K[i][j] = '1'
        charge = I.scalar_budget(grams, 3)
        self.assertEqual(charge['storage_zKz'], '1')
        self.assertEqual(charge['storage_contribution'], '-6')
        self.assertEqual(A.scalar_budget(grams, 3)['total'], charge['total'])
        out = I.build_blocks(3)
        child, parent, delta = I.increment_polynomials(K, out['blocks'], out['storage_blocks'], 11)
        self.assertEqual(delta.get((), F(0)), F(-6))
        self.assertEqual(child.get((), F(0)), F(6))
        self.assertEqual(parent.get((), F(0)), F(3))
        K[6][7] = K[7][6] = '-1'
        self.assertEqual(I.scalar_budget(grams, 3)['storage_zKz'], '0')
        self.assertEqual(I.initial_cost(K)['S_R_1'], '1')
        # The exact X1 state is prefix + mod3one, so this cross term survives.
        K = zero()
        for i in (1, 4):
            for j in (1, 4): K[i][j] = '1'
        self.assertEqual(I.initial_cost(K)['S_R_1'], '5')

    def test_dual_complete_moments_and_factor_two(self):
        fixture = toy(dual=True, cross=True)
        checked = self.check(fixture, dual=True)
        self.assertTrue(checked['complete_moments_verified'])
        self.assertEqual(checked['full_Gram_dual_matrices']['storage_K'][2][2], '5')
        self.assertEqual(checked['full_Gram_dual_matrices']['storage_K'][1][2], '5')
        self.assertEqual(fixture[3]['gram_columns_dot_y'][-104], '10')
        bad = copy.deepcopy(fixture); bad[3]['gram_duals']['storage_K']['matrix'][2][2] = '8'
        with self.assertRaises(ValueError): self.check(bad, dual=True)
        bad = copy.deepcopy(fixture); bad[3]['gram_columns_dot_y'][-104] = '5'
        with self.assertRaises(ValueError): self.check(bad, dual=True)
        bad = copy.deepcopy(fixture); bad[3]['weights'].pop(); bad[3]['monomials'].pop()
        with self.assertRaises(ValueError): self.check(bad, dual=True)
        bad = copy.deepcopy(fixture); bad[3]['weights'].append('0'); bad[3]['monomials'].append(dict(instance=0, m=[1, 1, 1]))
        with self.assertRaises(ValueError): self.check(bad, dual=True)

    def test_old_witness_invalidity_is_not_feasibility(self):
        # Regional matrices stay PSD, but child-minus-four-parent is negative.
        fixture = toy(dual=True)
        fixture[1][0]['full_child'][0][2] = [dict(m=[1], c='1')]
        fixture[2][0] = I.storage_transport(fixture[1][0])
        fixture[3]['gram_block_hashes'] = list(map(I.I.digest, fixture[1]))
        fixture[3]['storage_block_hashes'] = list(map(I.I.digest, fixture[2]))
        fixture[3]['gram_duals']['full_child']['matrix'][2][2] = '1'
        fixture[3]['gram_duals']['storage_K']['matrix'][2][2] = '-3'
        with self.assertRaises(ValueError): self.check(fixture, dual=True)

    def test_finite_claim_promotion_rejected(self):
        for dual in (False, True):
            for key in ('global_bound_proved', 'RH_proved', 'uniform_innovation_bound_proved', 'larger_cone_feasibility_proved'):
                fixture = toy(dual=dual); fixture[3][key] = True
                with self.assertRaises(ValueError): self.check(fixture, dual=dual)
            fixture = toy(dual=dual); fixture[3]['grammar_hash'] = '0'*64
            with self.assertRaises(ValueError): self.check(fixture, dual=dual)

    def test_half_fiber_boundary_identity(self):
        self.assertEqual(I.half_energy_identity(1)['half_energy'], [])
        for X in (2, 4, 6):
            result = I.half_energy_identity(X)
            self.assertEqual(result['half_energy'], result['twice_previous_energy'])
        with self.assertRaises(ValueError): I.half_energy_identity(3)

    def test_unit_prepended_to_every_complete_row(self):
        for X in (1, 2, 3):
            source = I.build_blocks(X)
            old = I.B.build_blocks(X)
            for group, rows in source['blocks'].items():
                self.assertEqual(len(rows), X*(2 if group.endswith('child') else 1))
                for row, original in zip(rows, old['blocks'][group]):
                    self.assertEqual(row[0], [dict(m=[], c='1')])
                    self.assertEqual(row[1:], original)
                    self.assertEqual(len(row), 15)
            self.assertEqual(source['storage_blocks']['child'], source['blocks']['full_child'])
            self.assertEqual(source['storage_blocks']['parent'], source['blocks']['full_parent'])

    def test_rehashed_unit_or_final_channel_omission_rejected(self):
        for kind in ('unit_missing', 'unit_nonconstant', 'unit_two', 'last_channel'):
            fixture = toy(dual=True)
            row = fixture[1][0]['full_child'][0]
            if kind == 'unit_missing': row[0] = []
            elif kind == 'unit_nonconstant': row[0] = [dict(m=[1], c='1')]
            elif kind == 'unit_two': row[0] = [dict(m=[], c='2')]
            else: row.pop()
            fixture[2][0] = I.storage_transport(fixture[1][0])
            fixture[3]['gram_block_hashes'] = list(map(I.I.digest, fixture[1]))
            fixture[3]['storage_block_hashes'] = list(map(I.I.digest, fixture[2]))
            with self.assertRaises(ValueError): self.check(fixture, dual=True)

    def test_affine_linear_moment_is_required_and_not_zero_filled(self):
        fixture = toy(dual=True)
        domain = [(row['instance'], tuple(row['m'])) for row in fixture[3]['monomials']]
        self.assertIn((0, (1,)), domain)
        k = domain.index((0, (1,)))
        fixture[3]['monomials'].pop(k); fixture[3]['weights'].pop(k)
        with self.assertRaisesRegex(ValueError, 'complete anchored dual coefficient domain'):
            self.check(fixture, dual=True)

    def test_zero_unit_moment_nonzero_first_moment_is_not_PSD(self):
        fixture = toy(dual=True)
        domain = [(row['instance'], tuple(row['m'])) for row in fixture[3]['monomials']]
        fixture[3]['weights'][domain.index((0, (1,)))] = '1'
        # Scalar signs and target still pass. Exact full15 PSD must reject the
        # nonzero first row even if the archived old14 principal block is PSD.
        with self.assertRaisesRegex(ValueError, 'zero diagonal nonzero offdiagonal'):
            self.check(fixture, dual=True)

    def test_unit_divisor_cross_scalar_and_actual_boundary_differ(self):
        grams = {g: zero() for g in I.gram_specs()}
        for group in grams:
            for i in (0, 6):
                for j in (0, 6): grams[group][i][j] = '1'
        # (1-1/2)^2=1/4 formally; at t1 divisor contrast is zero,
        # so the unit storage square is exactly one and S_R(1)=2.
        scalar = I.scalar_budget(grams, 3)
        self.assertEqual(scalar['storage_zKz'], '1/4')
        self.assertEqual([row['contribution'] for row in scalar['ledger']], ['3/2', '3/4', '-3/2'])
        self.assertEqual(scalar['total'], '3/4')
        self.assertEqual(scalar['linear_coefficient'], '1/4')
        self.assertEqual(A.scalar_budget(grams, 3)['ledger'], scalar['ledger'])
        initial = I.initial_cost(grams['storage_K'])
        self.assertEqual(initial['S_R_1'], '2')
        self.assertEqual(initial['unit_state'], I.SPEC['actual_initial_vector'])
        self.assertNotEqual(initial['unit_state'], I.SPEC['constant_vector'])
        source = I.build_blocks(3)
        for group in ('full_child', 'full_parent'):
            polynomial = I.I.gram_polynomial(grams[group], source['blocks'][group], 11)
            entry = next(row for row in scalar['ledger'] if row['group'] == group)
            self.assertEqual(polynomial.get((), F(0)), F(entry['contribution']))
        delta = I.increment_polynomials(grams['storage_K'], source['blocks'], source['storage_blocks'], 11)[2]
        self.assertEqual(delta[()], F('-3/2'))

    def test_old_full14_embedding_preserves_polynomials_charges_initial_cost(self):
        old = {g: [['0']*14 for _ in range(14)] for g in I.OLD.gram_specs()}
        for group in old:
            for i in (0, 3, 5):
                for j in (0, 3, 5): old[group][i][j] = '1'
        grams = I.embed_anchored_grams(old)
        self.assertEqual(grams, A.embed_anchored_grams(old))
        for matrix in grams.values():
            self.assertEqual(matrix[0], ['0']*15)
            self.assertTrue(all(row[0] == '0' for row in matrix))
        for X in (1, 2):
            affine = I.build_blocks(X); original = I.OLD.build_blocks(X)
            for group in I.regional_specs():
                self.assertEqual(I.I.gram_polynomial(grams[group], affine['blocks'][group], 4*X-1),
                                 I.I.gram_polynomial(old[group], original['blocks'][group], 4*X-1))
            self.assertEqual(I.scalar_budget(grams, X)['total'], I.OLD.scalar_budget(old, X)['total'])
        self.assertEqual(I.initial_cost(grams['storage_K'])['S_R_1'], I.OLD.initial_cost(old['storage_K'])['S_R_1'])
        base = {group: old[group] for group in I.B.gram_specs()}
        self.assertEqual(I.embed_base_grams(base), A.embed_base_grams(base))
        bad = copy.deepcopy(old); bad['storage_K'][1][1] = '-1'
        with self.assertRaises(ValueError): I.embed_anchored_grams(bad)

    def test_gamma_auxiliary_has_no_affine_rows(self):
        old = I.B.auxiliary(); affine = I.auxiliary()
        self.assertEqual(affine['instance'], old['instance'])
        for rows in affine['gram_blocks'].values(): self.assertEqual(rows, [])
        self.assertEqual(affine['storage_blocks']['child'], [])
        self.assertEqual(affine['storage_blocks']['parent'], [])
        system = I.coefficient_system([affine['instance']], [affine['gram_blocks']], [affine['storage_blocks']])
        self.assertEqual(len(system['columns'])-system['offset'], 360)
        self.assertTrue(all(not column for column in system['columns'][system['offset']:]))
        self.assertIn('necessary gate only', affine['scope'])

    def test_exact_complete_scalar_extraction_retains_storage_sign(self):
        instance = dict(target='mu', horizon=1, lhs=[dict(m=[], c='10')],
                        square_groups=[[dict(weight='3', poly=[dict(m=[1], c='1')])],
                                       [dict(weight='2', poly=[dict(m=[], c='1')])]],
                        relation_groups=[[dict(spec=dict(kind='unit'), multiplier=[dict(m=[], c='1')])]])
        grams = {g: zero() for g in I.gram_specs()}; grams['storage_K'][0][0] = '1'
        weights = dict(square_weights=['7', '2'], relation_weights=['3'])
        out = I.extract_scalar_budget(instance, weights, grams, 3)
        self.assertEqual(out['original_scalar_budget'], '1') # 0 + 4 - 3
        self.assertEqual(out['matrix_budget']['total'], '-6')
        self.assertEqual(out['B'], '-5')
        self.assertEqual(out['scalar_slack'], '15')
        self.assertFalse(out['nonconstant_identity_verified'])
        for bad in ({**weights, 'square_weights': ['-1', '2']},
                    {**weights, 'relation_weights': []}):
            with self.assertRaises(ValueError): I.extract_scalar_budget(instance, bad, grams, 3)

    def test_regional_psd_and_scalar_slack_remain_required(self):
        for kind in ('regional_nonPSD', 'negative_slack', 'changed_budget', 'state_anchor_unit'):
            fixture = toy()
            if kind == 'regional_nonPSD': fixture[3]['grams']['full_parent'][0][0] = '-1'
            elif kind == 'negative_slack': fixture[3]['constant_slacks'] = ['-1']
            elif kind == 'changed_budget':
                fixture[0][0]['lhs'][0]['c'] = '2'
                fixture[3]['source_hashes'] = list(map(I.I.digest, fixture[0]))
            else:
                fixture[3]['state_matrix'] = I.anchored_matrix(fixture[3]['grams']['storage_K'])
                fixture[3]['state_matrix'][1][1] = '0'; fixture[3]['state_matrix'][0][0] = '1'
            with self.assertRaises(ValueError): self.check(fixture)

    def test_affine_primal_unit_cross_and_negative_parent_are_transport(self):
        fixture = toy(); instances, blocks, storage, result = fixture
        K = zero()
        for i in (0, 2):
            for j in (0, 2): K[i][j] = '1'
        result['grams']['storage_K'] = K
        child, parent, delta = I.increment_polynomials(K, blocks[0], storage[0], 1)
        self.assertEqual(delta, {(): F(-3), (1,): F(-2), (1, 1): F(5)})
        instances[0]['lhs'] = I.P.canonical(I.P.add({(): F(1)}, delta))
        result['source_hashes'] = list(map(I.I.digest, instances))
        result['certificates'] = [S.instantiate_certificate(instances[0], result['weights'], result['grams'], blocks[0], storage[0])]
        result['exact_column_weights'] = ['1', '0']+[result['grams'][g][i][j] for g in sorted(I.gram_specs()) for i in range(15) for j in range(i, 15)]
        checked = self.check(fixture)
        self.assertTrue(checked['signed_increment_identity_verified'])
        self.assertFalse(checked['storage_is_nonnegative_SOS'])
        self.assertEqual(checked['initial_cost']['S_R_1'], '2')
        self.assertEqual(result['certificates'][0]['transformed_lhs'], [dict(m=[], c='1')])

    def test_child_gram_reparameterization_preserves_full15_RHS_and_charge(self):
        grams = {g: zero() for g in I.gram_specs()}
        for group, indices in [('full_child', (0, 1, 6)), ('full_parent', (0, 4)), ('storage_K', (1, 7))]:
            for i in indices:
                for j in indices: grams[group][i][j] = '1'
        reduced = {g: zero() for g in I.gram_specs()}
        for i in range(15):
            for j in range(15):
                reduced['storage_K'][i][j] = str(F(grams['storage_K'][i][j])+F(grams['full_child'][i][j]))
                reduced['full_parent'][i][j] = str(F(grams['full_parent'][i][j])+4*F(grams['full_child'][i][j]))
        for matrix in reduced.values(): I.I.verify_psd(matrix)
        for X in (1, 2, 3):
            source = I.build_blocks(X)
            def rhs(matrices):
                out = I.increment_polynomials(matrices['storage_K'], source['blocks'], source['storage_blocks'], 4*X-1)[2]
                for group in I.regional_specs():
                    out = I.P.add(out, I.I.gram_polynomial(matrices[group], source['blocks'][group], 4*X-1))
                return out
            self.assertEqual(rhs(grams), rhs(reduced))
            self.assertEqual(I.scalar_budget(grams, X)['total'], I.scalar_budget(reduced, X)['total'])
        u = list(map(F, I.SPEC['actual_initial_vector']))
        increase = sum((u[i]*F(grams['full_child'][i][j])*u[j] for i in range(15) for j in range(15)), F(0))
        self.assertEqual(F(I.initial_cost(reduced['storage_K'])['S_R_1'])-F(I.initial_cost(grams['storage_K'])['S_R_1']), increase)


if __name__ == '__main__':
    unittest.main()
