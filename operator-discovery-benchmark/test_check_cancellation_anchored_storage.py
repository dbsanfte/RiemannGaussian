"""Independent finite-admission regressions, with no research scoring."""
import ast
import copy
from fractions import Fraction as F
from pathlib import Path
import unittest
import check_cancellation_anchored_storage as I
import cancellation_anchored_storage as A
import cancellation_anchored_storage_synthesis as S


def zero():
    return [['0']*14 for _ in range(14)]


def toy(dual=False, K0=False, cross=False):
    atom = [dict(m=[1], c='1')]
    parent = [[] for _ in range(14)]; parent[1] = atom
    child = [[] for _ in range(14)]; child[1] = [dict(m=[1], c='3')]
    if cross:
        parent[0] = copy.deepcopy(parent[1]); child[0] = copy.deepcopy(child[1])
    blocks = [dict(full_child=[child], full_parent=[parent])]
    storage = [I.storage_transport(blocks[0])]
    lhs = [dict(m=[1, 1], c='-1')] if dual else [dict(m=[], c='1')]+([] if K0 else [dict(m=[1, 1], c='5')])
    instances = [dict(target='mu', horizon=1, lhs=lhs,
                      square_groups=[] if dual else [[dict(weight='1', poly=[dict(m=[], c='1')])]], relation_groups=[])]
    grams = {g: zero() for g in I.gram_specs()}
    if not K0:
        grams['storage_K'][1][1] = '1'
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
            for i in range(14):
                for j in range(i, 14):
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
        upper = [grams[g][i][j] for g in sorted(I.gram_specs()) for i in range(14) for j in range(i, 14)]
        result['exact_column_weights'] = ['1', '0']+upper
    return instances, blocks, storage, result


class AnchoredChecker(unittest.TestCase):
    def check(self, fixture, dual=False):
        instances, blocks, storage, result = fixture
        return (I.verify_dual if dual else I.verify_primal)(instances, blocks, storage, I.gram_specs(), result)

    def test_no_producer_imports(self):
        source = Path(I.__file__).read_text()
        imports = [node.module for node in ast.walk(ast.parse(source)) if isinstance(node, ast.ImportFrom)]
        imports += [name.name for node in ast.walk(ast.parse(source)) if isinstance(node, ast.Import) for name in node.names]
        self.assertFalse(any(name and name.startswith('cancellation_anchored') for name in imports))
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
            bad = copy.deepcopy(out); bad['gram_blocks']['full_child'][0][5] = []
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
        self.assertEqual(len(cols)-offset, 315)

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
            else: storage['child'][0][1] = []
            fixture[3]['storage_block_hashes'] = list(map(I.I.digest, fixture[2]))
            with self.assertRaises(ValueError):
                self.check(fixture)

    def test_wrong_K_and_target_rearrangement(self):
        for edit in ('K', 'increment', 'transformed', 'original', 'negative_parent_SOS'):
            fixture = copy.deepcopy(toy()); record = fixture[3]['certificates'][0]
            if edit == 'K': record['storage_proof']['K'][1][1] = '2'
            elif edit == 'increment': record['storage_proof']['polynomial'] = []
            elif edit == 'transformed': record['transformed_lhs'] = fixture[0][0]['lhs']
            elif edit == 'original': record['original_lhs'] = []
            else:
                record['transformed_target_certificate']['squares'].append(dict(weight='-4', poly=[dict(m=[1], c='1')]))
            with self.assertRaises(ValueError):
                self.check(fixture)

    def test_nonPSD_coercivity_even_when_R_PSD(self):
        K = zero(); K[0][0] = '-1/2'
        R = zero(); R[0][0] = '1/2'
        self.assertTrue(I.I.verify_psd(R)['PSD_verified'])
        with self.assertRaises(ValueError):
            I.anchored_matrix(K)
        fixture = copy.deepcopy(toy()); fixture[3]['grams']['storage_K'] = K
        with self.assertRaises(ValueError):
            self.check(fixture)

    def test_all_cross_constants_and_initial_cost(self):
        grams = {g: zero() for g in I.gram_specs()}
        K = grams['storage_K']
        for i in (5, 6):
            for j in (5, 6): K[i][j] = '1'
        charge = I.scalar_budget(grams, 3)
        self.assertEqual(charge['storage_zKz'], '1')
        self.assertEqual(charge['storage_contribution'], '-6')
        self.assertEqual(A.scalar_budget(grams, 3)['total'], charge['total'])
        out = I.build_blocks(3)
        child, parent, delta = I.increment_polynomials(K, out['blocks'], out['storage_blocks'], 11)
        self.assertEqual(delta.get((), F(0)), F(-6))
        self.assertEqual(child.get((), F(0)), F(6))
        self.assertEqual(parent.get((), F(0)), F(3))
        K[5][6] = K[6][5] = '-1'
        self.assertEqual(I.scalar_budget(grams, 3)['storage_zKz'], '0')
        self.assertEqual(I.initial_cost(K)['S_R_1'], '1')
        # The exact X1 state is prefix + mod3one, so this cross term survives.
        K = zero()
        for i in (0, 3):
            for j in (0, 3): K[i][j] = '1'
        self.assertEqual(I.initial_cost(K)['S_R_1'], '5')

    def test_dual_complete_moments_and_factor_two(self):
        fixture = toy(dual=True, cross=True)
        checked = self.check(fixture, dual=True)
        self.assertTrue(checked['complete_moments_verified'])
        self.assertEqual(checked['full_Gram_dual_matrices']['storage_K'][1][1], '5')
        self.assertEqual(checked['full_Gram_dual_matrices']['storage_K'][0][1], '5')
        self.assertEqual(fixture[3]['gram_columns_dot_y'][-104], '10')
        bad = copy.deepcopy(fixture); bad[3]['gram_duals']['storage_K']['matrix'][1][1] = '8'
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
        fixture[1][0]['full_child'][0][1] = [dict(m=[1], c='1')]
        fixture[2][0] = I.storage_transport(fixture[1][0])
        fixture[3]['gram_block_hashes'] = list(map(I.I.digest, fixture[1]))
        fixture[3]['storage_block_hashes'] = list(map(I.I.digest, fixture[2]))
        fixture[3]['gram_duals']['full_child']['matrix'][1][1] = '1'
        fixture[3]['gram_duals']['storage_K']['matrix'][1][1] = '-3'
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


if __name__ == '__main__':
    unittest.main()
