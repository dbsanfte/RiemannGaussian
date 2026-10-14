"""Complete regional mixing of every existing legacy and divisor atom.

This is a deterministic union of the prior groups, identifying their common
prefix atom. Scalar sources, complements, targets and auxiliary gate are kept.
"""
from fractions import Fraction as F
import copy
import cancellation_joint_gram_program as OLD

C = OLD.C
SPEC = dict(version='complete-regional-grams-v1', scalar_language=C.SPEC,
            atoms=OLD.SPEC['legacy_atoms'] + OLD.SPEC['joint_atoms'][1:],
            regions=['parent', 'child'], dimension=14,
            matrix_sharing='one exact PSD matrix per region, shared across every t and X',
            constant_vector=['0'] * 5 + ['-1/2'] * 9,
            selection='union of every prior regional atom; identify shared prefix; retain every pair',
            auxiliary_blocks='empty for every Gram group')


def group_descriptors():
    return {name: dict(kind='complete_arithmetic', region=region, dimension=14,
                       atoms=copy.deepcopy(SPEC['atoms']), normalizer='unit_constant')
            for name, region in [('full_child', 'child'), ('full_parent', 'parent')]}


def gram_specs():
    return {'full_child': 14, 'full_parent': 14}


def assemble_blocks(X, old):
    blocks, archive = {}, {}
    for name, desc in group_descriptors().items():
        region = desc['region']
        ts = list(range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X))
        legacy, joint = old['old_' + region], old['joint_' + region]
        if len(legacy) != len(ts) or len(joint) != len(ts):
            raise ValueError('complete regional block coverage')
        rows = []
        for a, b in zip(legacy, joint):
            if len(a) != 5 or len(b) != 10 or a[0] != b[0]:
                raise ValueError('exact shared prefix and complete atom dimensions')
            rows.append(a + b[1:])
        blocks[name] = rows
        archive[name] = dict(descriptor=desc, scales=ts, blocks_sha256=C.digest(rows),
                             block_count=len(rows), complete_source=True)
    return dict(blocks=blocks, archive=archive, gram_specs=gram_specs(),
                global_bound_proved=False, RH_proved=False)


def build_blocks(X, **limits):
    old = OLD.build_blocks(X, **limits)
    out = assemble_blocks(X, old['blocks'])
    out['construction_operations'] = old['construction_operations']
    return out


def build(program, X, **limits):
    out = OLD.build(program, X, **limits)
    data = assemble_blocks(X, out['gram_blocks'])
    out.update(gram_blocks=data['blocks'], gram_archive=data['archive'],
               gram_specs=gram_specs(), gram_program=SPEC)
    return out


def auxiliary():
    out = OLD.auxiliary()
    out.update(gram_blocks={name: [] for name in gram_specs()}, gram_specs=gram_specs())
    return out


def scalar_budget(grams, X):
    if type(X) is not int or X < 1 or type(grams) is not dict or set(grams) != set(gram_specs()):
        raise ValueError('complete Gram dictionary and positive scale')
    ledger = []
    for name in gram_specs():
        matrix = grams[name]
        if len(matrix) != 14 or any(len(row) != 14 for row in matrix):
            raise ValueError('complete Gram dimensions')
        matrix = [[F(q) for q in row] for row in matrix]
        if any(matrix[i][j] != matrix[j][i] for i in range(14) for j in range(14)):
            raise ValueError('symmetric Gram required')
        charge = sum((matrix[i][j] for i in range(5, 14) for j in range(5, 14)), F(0)) * X / 4
        if name == 'full_child':
            charge *= 2
        ledger.append(dict(group=name, contribution=str(charge)))
    return dict(total=str(sum((F(row['contribution']) for row in ledger), F(0))), ledger=ledger,
                PSD_verified=False, scope='formal scalar extraction; PSD checked separately',
                global_bound_proved=False, RH_proved=False)
