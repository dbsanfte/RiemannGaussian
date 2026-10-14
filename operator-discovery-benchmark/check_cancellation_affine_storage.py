"""Independent exact checker for signed affine full15 anchored storage.

Imports only the independently reconstructed base source and checker algebra.
The negative parent block is a transport term, never a nonnegative SOS.
"""
import copy
from fractions import Fraction as F
import check_cancellation_complete_gram_program as B
import check_cancellation_shared_gram as I
import check_cancellation_anchored_storage as OLD

P = I.P
FLAGS = dict(global_bound_proved=False, RH_proved=False)
SPEC = dict(version='affine-anchored-full15-storage-v1', base_program=B.SPEC,
            atoms=['unit']+copy.deepcopy(B.SPEC['atoms']), dimension=15,
            anchor='prefix', anchor_index=1, storage_matrix='R=e_prefix e_prefix^T+K; K PSD',
            matrix_sharing='one fixed K shared across every t and X',
            transport_kind='signed_storage_increment', child_multiplier='1', parent_multiplier='-4',
            target_identity='D-Delta(E)=nonnegative_proof_terms+Delta(S_K)',
            constant_vector=['1']+['0']*5+['-1/2']*9,
            actual_initial_vector=['1','1','0','0','1']+['0']*10,
            formal_storage_scalar='-2 X z^T K z', auxiliary_storage_blocks='empty',
            gamma_zero_scope='necessary gate conditional on unchanged fixed-template scalar-growth assumptions',
            selection='prepend constant unit to every regional and storage state; retain all 120 upper pairs')


def gram_specs():
    return dict(full_child=15, full_parent=15, storage_K=15)


def storage_transport(blocks):
    if type(blocks) is not dict or set(blocks) != set(B.gram_specs()):
        raise ValueError('complete regional storage source')
    return dict(kind='signed_storage_increment', child=copy.deepcopy(blocks['full_child']),
                parent=copy.deepcopy(blocks['full_parent']), child_multiplier='1', parent_multiplier='-4')


def verify_transport(blocks, transport, horizon):
    if type(transport) is not dict or transport != storage_transport(blocks):
        raise ValueError('exact typed signed child-minus-four-parent storage source')
    for rows in blocks.values():
        if type(rows) is not list:
            raise ValueError('regional block list')
        for atoms in rows:
            if type(atoms) is not list or len(atoms) != 15:
                raise ValueError('ordered full15 storage atoms')
            if P.parse(atoms[0], horizon) != {(): F(1)}:
                raise ValueError('constant unit in every affine regional row')
            for atom in atoms:
                P.parse(atom, horizon)
    return dict(verified=True, storage_is_nonnegative_SOS=False, **FLAGS)


def regional_specs():
    return dict(full_child=15, full_parent=15)


def group_descriptors():
    return {name: dict(kind='complete_affine_arithmetic', region=region,
                      dimension=15, atoms=copy.deepcopy(SPEC['atoms']), normalizer='unit_constant')
            for name, region in [('full_child', 'child'), ('full_parent', 'parent')]}


def assemble_blocks(X, old):
    if type(X) is not int or X < 1 or type(old) is not dict or set(old) != set(B.gram_specs()):
        raise ValueError('complete independent full14 regional source')
    blocks = {}; archive = {}
    for name, descriptor in group_descriptors().items():
        rows = old[name]
        count = X*(1 if descriptor['region'] == 'parent' else 2)
        if type(rows) is not list or len(rows) != count:
            raise ValueError('complete affine regional block count')
        if any(type(row) is not list or len(row) != 14 for row in rows):
            raise ValueError('complete original atom rows')
        lifted = [[P.canonical({(): F(1)})]+copy.deepcopy(row) for row in rows]
        blocks[name] = lifted
        archive[name] = dict(descriptor=descriptor,
                             scales=list(range(X, 2*X) if descriptor['region'] == 'parent' else range(2*X, 4*X)),
                             blocks_sha256=I.digest(lifted), block_count=count, complete_source=True)
    return dict(blocks=blocks, archive=archive, gram_specs=gram_specs(), **FLAGS)


def build(program, X, **limits):
    out = B.build(program, X, **limits)
    data = assemble_blocks(X, out['gram_blocks'])
    out.update(gram_blocks=data['blocks'], gram_archive=data['archive'],
               storage_blocks=storage_transport(data['blocks']),
               gram_specs=gram_specs(), gram_program=copy.deepcopy(SPEC))
    return out


def build_blocks(X, **limits):
    out = assemble_blocks(X, B.build_blocks(X, **limits)['blocks'])
    out.update(storage_blocks=storage_transport(out['blocks']))
    return out


def auxiliary():
    out = B.auxiliary()
    out.update(gram_specs=gram_specs(), storage_blocks=storage_transport(out['gram_blocks']))
    return out


def embed_anchored_grams(grams):
    """Exact zero-unit-row congruence embedding of the old anchored full14 cone."""
    if type(grams) is not dict or set(grams) != set(OLD.gram_specs()):
        raise ValueError('complete original anchored full14 matrices')
    out = {}
    for group in gram_specs():
        matrix = grams[group]
        if type(matrix) is not list or len(matrix) != 14:
            raise ValueError('original full14 matrix dimension')
        I.verify_psd(matrix)
        lifted = [[F(0)]*15 for _ in range(15)]
        for i in range(14):
            for j in range(14):
                lifted[i+1][j+1] = I.rational(matrix[i][j])
        I.verify_psd(lifted)
        out[group] = [[str(q) for q in row] for row in lifted]
    return out


def embed_base_grams(grams):
    if type(grams) is not dict or set(grams) != set(B.gram_specs()):
        raise ValueError('both original full14 regional matrices')
    old = copy.deepcopy(grams)
    old['storage_K'] = [['0']*14 for _ in range(14)]
    return embed_anchored_grams(old)


def check_builder(program, X, out, **limits):
    expected = build(program, X, **limits)
    ignored = {'construction_operations', 'gram_program_operations', 'cell_construction_operations', 'construction_cost'}
    if type(out) is not dict or set(out)-ignored != set(expected)-ignored:
        raise ValueError('anchored source builder fields')
    for key in set(expected)-ignored:
        if I.digest(out[key]) != I.digest(expected[key]):
            raise ValueError('independently rebuilt anchored source '+key)
    return dict(verified=True, complete_sources_verified=True,
                producer_operation_count_independently_verified=False, **FLAGS)


def anchored_matrix(K):
    if type(K) is not list or len(K) != 15:
        raise ValueError('full15 storage matrix')
    I.verify_psd(K)
    R = [[I.rational(v) for v in row] for row in K]
    R[1][1] += 1
    remainder = [[R[i][j]-int(i == j == 1) for j in range(15)] for i in range(15)]
    I.verify_psd(remainder)
    I.verify_psd(R)
    return [[str(v) for v in row] for row in R]


def initial_cost(K):
    """S_R(1) from the full unit-scale state, using only the unit x_1=1."""
    R = anchored_matrix(K)
    rows = build_blocks(1)['blocks']['full_parent']
    if len(rows) != 1:
        raise ValueError('complete X1 parent boundary')
    values = []
    for atom in rows[0]:
        p = P.parse(atom, 1)
        values.append(sum(p.values(), F(0)))
    expected = [F(1), F(1), F(0), F(0), F(1), F(0)]+[F(0)]*9
    if values != expected:
        raise ValueError('complete X1 unit, masks and divisor boundaries')
    initial = sum((values[i]*F(R[i][j])*values[j] for i in range(15) for j in range(15)), F(0))
    if initial < 1:
        raise ValueError('initial prefix coercivity')
    return dict(initial_scale=1, unit_state=list(map(str, values)), S_R_1=str(initial),
                E_1='1', initial_cost_finite=True, actual_initial_vector=list(map(str, values)),
                storage_initial_cost=str(initial-1), anchored_initial_cost=str(initial),
                formal_vector_is_initial_state=False, **FLAGS)


def scalar_budget(grams, X):
    if type(X) is not int or X < 1 or type(grams) is not dict or set(grams) != set(gram_specs()):
        raise ValueError('anchored matrices and positive scale')
    z = list(map(F, SPEC['constant_vector']))
    ledger = []
    for group in regional_specs():
        matrix = grams[group]
        if type(matrix) is not list or len(matrix) != 15:
            raise ValueError('affine full15 regional dimension')
        I.verify_psd(matrix)
        zGz = sum((z[i]*I.rational(matrix[i][j])*z[j] for i in range(15) for j in range(15)), F(0))
        charge = X*(1 if group == 'full_parent' else 2)*zGz
        ledger.append(dict(group=group, contribution=str(charge)))
    total = sum((F(row['contribution']) for row in ledger), F(0))
    out = dict(total=str(total), linear_coefficient=str(total/X), ledger=ledger, PSD_verified=True,
               formal_constant_vector=list(SPEC['constant_vector']), **FLAGS)
    K = grams['storage_K']; anchored_matrix(K)
    z = list(map(F, SPEC['constant_vector']))
    zKz = sum((z[i]*I.rational(K[i][j])*z[j] for i in range(15) for j in range(15)), F(0))
    charge = -2*X*zKz
    out['ledger'].append(dict(group='storage_K', contribution=str(charge), kind='signed_storage_increment'))
    out.update(total=str(F(out['total'])+charge), linear_coefficient=str((F(out['total'])+charge)/X), storage_zKz=str(zKz),
               storage_contribution=str(charge), storage_is_nonnegative_SOS=False,
               scope='formal exact constant extraction; fixed-matrix O(X), conditional necessary gate', **FLAGS)
    return out


def extract_scalar_budget(instance, weights, grams, X):
    """Complete formal scalar accounting, without substituting arithmetic values.

    A matching nonconstant identity remains a separate obligation. In particular,
    the negative storage constant is retained with its transport sign.
    """
    if type(weights) is not dict or set(weights) != {'square_weights', 'relation_weights'}:
        raise ValueError('complete shared scalar weights')
    sw = list(map(I.rational, weights['square_weights']))
    rw = list(map(I.rational, weights['relation_weights']))
    if any(q < 0 for q in sw):
        raise ValueError('nonnegative scalar square weights')
    lhs, squares, relations = I.scalar_columns(instance, sw, rw)
    original = sum((q*p.get((), F(0)) for q, p in zip(sw, squares)), F(0))
    original += sum((q*p.get((), F(0)) for q, p in zip(rw, relations)), F(0))
    matrix = scalar_budget(grams, X)
    budget = original+F(matrix['total'])
    target = lhs.get((), F(0))
    return dict(B=str(budget), D=str(target), scalar_slack=str(target-budget),
                original_scalar_budget=str(original), matrix_budget=matrix,
                nonconstant_identity_verified=False, **FLAGS)


def increment_polynomials(K, blocks, transport, horizon):
    verify_transport(blocks, transport, horizon)
    anchored_matrix(K)
    child = I.gram_polynomial(K, transport['child'], horizon)
    parent = I.gram_polynomial(K, transport['parent'], horizon)
    return child, parent, P.add(child, parent, F(-4))


def _coverage(instances, blocks, storage, specs):
    if specs != gram_specs() or type(instances) is not list or not instances:
        raise ValueError('nonempty anchored full15 specifications')
    if type(blocks) is not list or type(storage) is not list or len(blocks) != len(instances) or len(storage) != len(instances):
        raise ValueError('complete anchored instance coverage')
    for inst, row, transport in zip(instances, blocks, storage):
        verify_transport(row, transport, inst['horizon'])


def coefficient_system(instances, gram_blocks, storage_blocks, specs=None):
    """Rebuild every scalar and complete cross column; no missing coordinate is zero.

    Cross entries omit upper-triangle factor two, as moment matrix entries must.
    Columns include factor two, as symmetric primal matrix parameters require.
    """
    specs = gram_specs() if specs is None else specs
    _coverage(instances, gram_blocks, storage_blocks, specs)
    allcols = [I.G.columns(inst) for inst in instances]
    ns, nr = len(allcols[0][1]), len(allcols[0][2])
    domain = set(); cross = {}
    for k, (inst, blocks, transport, (lhs, sq, rel)) in enumerate(zip(instances, gram_blocks, storage_blocks, allcols)):
        if len(sq) != ns or len(rel) != nr:
            raise ValueError('shared scalar source dimensions')
        domain.add((k, ()))
        for p in [lhs]+sq+rel:
            domain.update((k, m) for m in p)
        parsed = {region: [[P.parse(a, inst['horizon']) for a in atoms] for atoms in blocks['full_'+region]] for region in ('child', 'parent')}
        for group in sorted(specs):
            for i in range(15):
                for j in range(i, 15):
                    p = {}
                    for region, scale in ([('child', F(1)), ('parent', F(-4))] if group == 'storage_K' else [(group[5:], F(1))]):
                        for atoms in parsed[region]:
                            p = P.add(p, P.multiply(atoms[i], atoms[j]), scale)
                    cross[group, i, j, k] = p
                    domain.update((k, m) for m in p)
    domain = sorted(domain)
    def stack(parts):
        return {(k, m): c for k, p in enumerate(parts) for m, c in p.items() if c}
    target = stack([row[0] for row in allcols])
    columns = [stack([row[1][j] for row in allcols]) for j in range(ns)]
    for j in range(nr):
        p = stack([row[2][j] for row in allcols]); columns.extend([p, {m: -c for m, c in p.items()}])
    columns.extend([{(k, ()): F(1)} for k in range(len(instances))])
    offset = len(columns)
    for group in sorted(specs):
        for i in range(15):
            for j in range(i, 15):
                columns.append(stack([{m: c*(1 if i == j else 2) for m, c in cross[group, i, j, k].items()} for k in range(len(instances))]))
    return dict(domain=domain, lhs=target, columns=columns, allcols=allcols,
                cross=cross, shape=(ns, nr, len(instances)), offset=offset, specs=dict(sorted(specs.items())))


def _bindings(instances, blocks, storage, specs, result):
    _coverage(instances, blocks, storage, specs)
    if result.get('global_bound_proved') is not False or result.get('RH_proved') is not False:
        raise ValueError('finite only anchored claim')
    for key in ('uniform_innovation_bound_proved', 'larger_cone_feasibility_proved'):
        if result.get(key, False) is not False:
            raise ValueError('unsupported finite promotion '+key)
    if result.get('gram_specs') != specs or result.get('source_hashes') != list(map(I.digest, instances)) or result.get('gram_block_hashes') != list(map(I.digest, blocks)) or result.get('storage_block_hashes') != list(map(I.digest, storage)):
        raise ValueError('anchored source and typed transport binding')
    if 'grammar_hash' in result and result['grammar_hash'] != I.digest(SPEC):
        raise ValueError('anchored grammar binding')


def verify_primal(instances, gram_blocks, storage_blocks, specs, result):
    _bindings(instances, gram_blocks, storage_blocks, specs, result)
    if result.get('status') != 'finite_PSD_certificate':
        raise ValueError('finite anchored primal required')
    grams = result['grams']
    if type(grams) is not dict or set(grams) != set(specs):
        raise ValueError('all anchored primal matrices')
    K = grams['storage_K']; R = anchored_matrix(K)
    if 'state_matrix' in result and result['state_matrix'] != R:
        raise ValueError('exact anchored coercivity matrix')
    if len(result['certificates']) != len(instances):
        raise ValueError('anchored certificate coverage')
    transformed = []; records = []
    for inst, blocks, transport, record in zip(instances, gram_blocks, storage_blocks, result['certificates']):
        child, parent, increment = increment_polynomials(K, blocks, transport, inst['horizon'])
        lhs = P.add(P.parse(inst['lhs'], inst['horizon']), increment, F(-1))
        if record.get('original_lhs') != inst['lhs'] or record.get('transformed_lhs') != P.canonical(lhs):
            raise ValueError('exact original-to-innovation target rearrangement')
        proof = record['storage_proof']
        expected = dict(kind='signed_storage_increment', K=K, child_multiplier='1', parent_multiplier='-4', child_polynomial=P.canonical(child), parent_polynomial=P.canonical(parent), polynomial=P.canonical(increment))
        if proof != expected:
            raise ValueError('typed signed storage increment polynomial proof')
        current = copy.deepcopy(inst); current['lhs'] = P.canonical(lhs); transformed.append(current)
        records.append(dict(certificate=record['transformed_target_certificate'], Gram_proofs=record['Gram_proofs'], constant_slack=record['constant_slack']))
    regional = copy.deepcopy(result)
    regional.update(gram_specs=regional_specs(), grams={k: grams[k] for k in B.gram_specs()},
                    source_hashes=list(map(I.digest, transformed)), certificates=records)
    regional.pop('exact_column_weights', None)
    checked = I.verify_primal(transformed, gram_blocks, regional_specs(), regional)
    if 'exact_column_weights' in result:
        vals = list(map(I.rational, result['exact_column_weights']))
        sw = list(map(I.rational, result['weights']['square_weights'])); rw = list(map(I.rational, result['weights']['relation_weights']))
        ns, nr = len(sw), len(rw); offset = ns+2*nr+len(instances)
        upper = [I.rational(grams[g][i][j]) for g in sorted(specs) for i in range(15) for j in range(i, 15)]
        if len(vals) != offset+len(upper) or vals[:ns] != sw or any(v < 0 for v in vals[:offset]) or [vals[ns+2*j]-vals[ns+2*j+1] for j in range(nr)] != rw or vals[ns+2*nr:offset] != list(map(F, result['constant_slacks'])) or vals[offset:] != upper:
            raise ValueError('exact anchored column weights')
    return dict(verified=True, transformed_target_check=checked, K_PSD_proof=I.verify_psd(K),
                state_matrix=R, coercivity_verified=True, signed_increment_identity_verified=True,
                initial_cost=initial_cost(K),
                storage_is_nonnegative_SOS=False, finite_only=True, **FLAGS)


def verify_dual(instances, gram_blocks, storage_blocks, specs, result):
    _bindings(instances, gram_blocks, storage_blocks, specs, result)
    if result.get('status') != 'exact_separator' or result.get('certified') is not True:
        raise ValueError('exact anchored separator required')
    system = coefficient_system(instances, gram_blocks, storage_blocks, specs)
    given = [(r['instance'], tuple(r['m'])) for r in result['monomials']]
    if given != system['domain'] or len(result['weights']) != len(given):
        raise ValueError('complete anchored dual coefficient domain')
    y = dict(zip(given, map(I.rational, result['weights'])))
    def dot(p):
        return sum((c*y[m] for m, c in p.items()), F(0))
    dots = list(map(dot, system['columns'])); lhs = dot(system['lhs'])
    if lhs >= 0 or any(q < 0 for q in dots[:system['offset']]):
        raise ValueError('anchored target and scalar separator signs')
    if list(map(I.rational, result['columns_dot_y'])) != dots[:system['offset']] or I.rational(result['lhs_dot_y']) != lhs:
        raise ValueError('anchored recorded scalar dual dots')
    ninstances = len(instances); ns, nr, _ = system['shape']; cd = [y[k, ()] for k in range(ninstances)]
    if 'constant_coordinates' in result and list(map(I.rational, result['constant_coordinates'])) != cd:
        raise ValueError('anchored recorded constant coordinates')
    if 'all_C_q_extension_requires_zero_constant_coordinates' in result and result['all_C_q_extension_requires_zero_constant_coordinates'] is not all(q == 0 for q in cd):
        raise ValueError('anchored all-budget extension claim')
    if type(result['gram_duals']) is not dict or set(result['gram_duals']) != set(specs):
        raise ValueError('anchored dual matrix coverage')
    matrices = {}; proofs = {}
    for group in sorted(specs):
        matrix = [[F(0)]*15 for _ in range(15)]
        for i in range(15):
            for j in range(i, 15):
                q = sum((c*y[k, m] for k in range(ninstances) for m, c in system['cross'][group, i, j, k].items()), F(0))
                matrix[i][j] = matrix[j][i] = q
        proofs[group] = I.verify_psd(matrix)
        matrices[group] = [[str(q) for q in row] for row in matrix]
        if result['gram_duals'][group]['matrix'] != matrices[group]:
            raise ValueError('complete anchored dual moment matrix '+group)
    expected_storage = [[str(F(matrices['full_child'][i][j])-4*F(matrices['full_parent'][i][j])) for j in range(15)] for i in range(15)]
    if matrices['storage_K'] != expected_storage:
        raise ValueError('exact storage moment child-minus-four-parent')
    if 'gram_columns_dot_y' in result and list(map(I.rational, result['gram_columns_dot_y'])) != dots[system['offset']:]:
        raise ValueError('anchored upper-triangle factor-two dual dots')
    return dict(verified=True, full_Gram_dual_matrices=matrices, PSD_proofs=proofs,
                complete_moments_verified=True, storage_is_nonnegative_SOS=False,
                declared_finite_cone_only=True, **FLAGS)


def half_energy_identity(X):
    """Exact source polynomials for the half-coordinate boundary, P_0=0."""
    if type(X) is not int or X < 1 or (X != 1 and X % 2):
        raise ValueError('X=1 or positive even integer scale')
    def prefix(t):
        return {(n,): F(1) for n in range(1, t+1)}
    def energy(a, b):
        out = {}
        for t in range(a, b):
            p = prefix(t); out = P.add(out, P.multiply(p, p))
        return out
    half = {}
    for t in range(X, 2*X):
        p = prefix(t//2); half = P.add(half, P.multiply(p, p))
    expected = {} if X == 1 else {m: 2*c for m, c in energy(X//2, X).items()}
    if half != expected:
        raise ValueError('complete half-energy floor fibers')
    return dict(verified=True, X=X, half_energy=P.canonical(half),
                twice_previous_energy=P.canonical(expected), X1_zero_boundary=X == 1, **FLAGS)
