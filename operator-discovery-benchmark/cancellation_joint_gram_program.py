"""Joint divisor-channel PSD language, retaining the complete scalar target.

One ten-atom matrix per region contains every former prefix/contrast pair.
The two five-atom legacy matrices remain independently available.
"""
from fractions import Fraction as F
import copy
import cancellation_cell_gram_program as OLD

C = OLD.C
SPEC = dict(version='joint-divisor-grams-v1', scalar_language=C.SPEC,
            legacy_atoms=['prefix', 'half', 'even', 'mod3one', 'prime'],
            joint_atoms=['prefix'] + [dict(theta=t, power=j) for t in ['1/3', '1/2', '2/3'] for j in [-1, 0, 1]],
            regions=['parent', 'child'], thetas=['1/3', '1/2', '2/3'], powers=[-1, 0, 1],
            matrix_sharing='one exact PSD matrix per group, shared across every t and X',
            joint_constant_vector=['0'] + ['-1/2'] * 9,
            auxiliary_blocks='empty for every Gram group')


def group_descriptors():
    groups = {}
    for region in SPEC['regions']:
        groups['old_' + region] = dict(kind='legacy', region=region, dimension=5,
                                      atoms=SPEC['legacy_atoms'])
        groups['joint_' + region] = dict(kind='joint_divisor_cells', region=region, dimension=10,
                                        atoms=SPEC['joint_atoms'], normalizer='unit_constant')
    return {k: copy.deepcopy(groups[k]) for k in sorted(groups)}


def gram_specs():
    return {k: d['dimension'] for k, d in group_descriptors().items()}


def build_blocks(X, *, additions=None, **limits):
    old = OLD.build_blocks(X, additions=additions, **limits)
    blocks, archive = {}, {}
    for name, desc in group_descriptors().items():
        region = desc['region']
        ts = list(range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X))
        if desc['kind'] == 'legacy':
            rows = old['blocks'][name]
        else:
            offset = 0 if region == 'parent' else 9
            sources = [old['blocks'][f'cell_{offset + i:03d}'] for i in range(9)]
            rows = []
            for k in range(len(ts)):
                prefix = sources[0][k][0]
                if any(source[k][0] != prefix for source in sources):
                    raise ValueError('joint prefix alignment')
                rows.append([prefix] + [source[k][1] for source in sources])
        blocks[name] = copy.deepcopy(rows)
        archive[name] = dict(descriptor=desc, scales=ts, blocks_sha256=C.digest(rows),
                             block_count=len(rows), complete_source=True)
    return dict(blocks=blocks, archive=archive, gram_specs=gram_specs(),
                construction_operations=old['construction_operations'],
                global_bound_proved=False, RH_proved=False)


def build(program, X, **limits):
    out = C.build_instance(program['target'], X, program['q'], program['C'], program['claim'], **limits)
    extra = dict(archive=out['cell_archive'], square_groups=out['instance']['square_groups'][-54:])
    data = build_blocks(X, additions=extra, **limits)
    out.update(gram_blocks=data['blocks'], gram_archive=data['archive'], gram_specs=gram_specs(),
               gram_program=SPEC, gram_program_operations=data['construction_operations'])
    return out


def auxiliary():
    out = OLD.auxiliary()
    out.update(gram_blocks={name: [] for name in gram_specs()}, gram_specs=gram_specs())
    return out


def scalar_budget(grams, X):
    """Exact formal constant c^T G c, including every contrast cross term."""
    if type(X) is not int or X < 1 or set(grams) != set(gram_specs()):
        raise ValueError('complete Gram dictionary/scale')
    ledger = []
    for name, desc in group_descriptors().items():
        matrix = grams[name]
        n = desc['dimension']
        if len(matrix) != n or any(len(row) != n for row in matrix):
            raise ValueError('Gram dimensions')
        values = [[F(q) for q in row] for row in matrix]
        if any(values[i][j] != values[j][i] for i in range(n) for j in range(n)):
            raise ValueError('symmetric Gram required')
        charge = F(0)
        if desc['kind'] == 'joint_divisor_cells':
            charge = sum((values[i][j] for i in range(1, n) for j in range(1, n)), F(0)) * X / 4
            if desc['region'] == 'child':
                charge *= 2
        ledger.append(dict(group=name, contribution=str(charge)))
    return dict(total=str(sum((F(r['contribution']) for r in ledger), F(0))), ledger=ledger,
                PSD_verified=False, scope='formal scalar extraction only; nonnegativity checked separately',
                global_bound_proved=False, RH_proved=False)
