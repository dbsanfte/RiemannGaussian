"""Complete cell Gram programs with shared learned matrices and scalar costs.

The scalar dictionary and target stay those of the frozen divisor-cell search.
New Grams allow all mixing ratios between the prefix and each divisor contrast.
"""
from fractions import Fraction as F
import copy
import cancellation_divisor_cell_language as C
import cancellation_arithmetic_templates as T
from cancellation_arithmetic_language import compile_expression
from cancellation_cubic_gate import build_constraint

SPEC = dict(version='cell-shared-grams-v1', scalar_language=C.SPEC,
            legacy_atoms=['prefix', 'half', 'even', 'mod3one', 'prime'],
            cell_atoms=['prefix', 'divisor_contrast'],
            regions=['parent', 'child'], thetas=['1/3', '1/2', '2/3'], powers=[-1, 0, 1],
            matrix_sharing='one exact PSD matrix per group, shared across every t and X',
            cell_constant_vector=['0', '-1/2'], auxiliary_blocks='empty for every Gram group')


def group_descriptors():
    groups = {}
    for region in SPEC['regions']:
        groups['old_' + region] = dict(kind='legacy', region=region, dimension=5,
                                      atoms=SPEC['legacy_atoms'])
    i = 0
    for region in SPEC['regions']:
        for theta in SPEC['thetas']:
            for power in SPEC['powers']:
                groups[f'cell_{i:03d}'] = dict(kind='divisor_cell', region=region,
                                              theta=theta, power=power, dimension=2,
                                              atoms=SPEC['cell_atoms'], normalizer='unit_constant')
                i += 1
    return {k: copy.deepcopy(groups[k]) for k in sorted(groups)}


def gram_specs():
    return {k: d['dimension'] for k, d in group_descriptors().items()}


def build_blocks(X, *, additions=None, max_horizon=80, max_operations=200000000,
                 max_terms=100000, max_coefficient_bits=4096):
    for n in [X, max_horizon, max_operations, max_terms, max_coefficient_bits]:
        if type(n) is not int or n < 1:
            raise ValueError('strict positive Gram program limits')
    H = 4 * X - 1
    if H > max_horizon:
        raise OverflowError('complete shared-Gram horizon')
    if additions is None:
        additions = C.build_additions(X, max_horizon=max_horizon, max_operations=max_operations,
                                      max_terms=max_terms, max_coefficient_bits=max_coefficient_bits)
    if len(additions['archive']) != 18 or len(additions['square_groups']) != 54:
        raise ValueError('complete 18-context source required')
    blocks, archive, operations = {}, {}, 0
    for name, desc in group_descriptors().items():
        region = desc['region']
        ts = list(range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X))
        out = []
        if desc['kind'] == 'legacy':
            for t in ts:
                row = []
                for atom in SPEC['legacy_atoms']:
                    compiled = compile_expression(T.contrast_ast(atom, t), X, H,
                                                  max_operations=max_operations - operations,
                                                  max_terms=max_terms, max_degree=12)
                    operations += compiled['operations']
                    row.append(compiled['poly'])
                out.append(row)
        else:
            i = int(name.split('_')[1])
            source = additions['archive'][i]
            if any(source[k] != desc[k] for k in ['region', 'theta', 'power']) or source['scales'] != ts:
                raise ValueError('complete cell descriptor/source binding')
            contrast_group = additions['square_groups'][3 * i]
            if len(contrast_group) != len(ts):
                raise ValueError('complete cell block coverage')
            for t, term in zip(ts, contrast_group):
                if term['weight'] != '1':
                    raise ValueError('unweighted contrast atom')
                out.append([[dict(m=[a], c='1') for a in range(1, t + 1)], copy.deepcopy(term['poly'])])
                operations += t + len(term['poly'])
        if operations > max_operations:
            raise OverflowError('Gram program construction work')
        blocks[name] = out
        archive[name] = dict(descriptor=desc, scales=ts, blocks_sha256=C.digest(out),
                             block_count=len(out), complete_source=True)
    return dict(blocks=blocks, archive=archive, gram_specs=gram_specs(),
                construction_operations=operations, global_bound_proved=False, RH_proved=False)


def build(program, X, **limits):
    out = C.build_instance(program['target'], X, program['q'], program['C'], program['claim'], **limits)
    extra = dict(archive=out['cell_archive'], square_groups=out['instance']['square_groups'][-54:])
    block_data = build_blocks(X, additions=extra, **limits)
    out.update(gram_blocks=block_data['blocks'], gram_archive=block_data['archive'], gram_specs=gram_specs(),
               gram_program=SPEC, gram_program_operations=block_data['construction_operations'])
    return out


def auxiliary():
    out = build_constraint(C.descriptors())
    out.update(gram_blocks={name: [] for name in gram_specs()}, gram_specs=gram_specs())
    return out


def scalar_budget(grams, X):
    if set(grams) != set(gram_specs()) or type(X) is not int or X < 1:
        raise ValueError('complete Gram dictionary/scale')
    ledger = []
    for name, d in group_descriptors().items():
        G = grams[name]
        if len(G) != d['dimension'] or any(len(row) != d['dimension'] for row in G):
            raise ValueError('Gram dimensions')
        charge = F(0)
        if d['kind'] == 'divisor_cell':
            charge = F(G[1][1]) * X * (1 if d['region'] == 'parent' else 2) / 4
        ledger.append(dict(group=name, contribution=str(charge)))
    return dict(total=str(sum((F(r['contribution']) for r in ledger), F(0))), ledger=ledger,
                PSD_verified=False, scope='formal scalar extraction only; nonnegativity checked separately',
                global_bound_proved=False, RH_proved=False)
