"""Typed anchored full14 storage, separate from the nonnegative SOS language.

R=e_prefix e_prefix^T+K, K PSD; only Delta(S_K) is transported. The
negative parent coefficient is never a Gram square weight.
"""
from fractions import Fraction as F
import copy
import cancellation_complete_gram_program as BASE
import cancellation_shared_gram_language as P

C = BASE.C
FLAGS = dict(global_bound_proved=False, RH_proved=False)
SPEC = dict(version='anchored-full14-storage-v1', base_program=BASE.SPEC,
            atoms=copy.deepcopy(BASE.SPEC['atoms']), dimension=14,
            anchor='prefix', anchor_index=0, storage_matrix='R=e_prefix e_prefix^T+K; K PSD',
            matrix_sharing='one fixed K shared across every t and X',
            transport_kind='signed_storage_increment', child_multiplier='1', parent_multiplier='-4',
            target_identity='D-Delta(E)=nonnegative_proof_terms+Delta(S_K)',
            constant_vector=['0']*5+['-1/2']*9,
            formal_storage_scalar='-2 X z^T K z', auxiliary_storage_blocks='empty',
            gamma_zero_scope='necessary gate conditional on unchanged fixed-template scalar-growth assumptions')

def gram_specs():
    return dict(full_child=14, full_parent=14, storage_K=14)

def storage_transport(blocks):
    if type(blocks) is not dict or set(blocks) != set(BASE.gram_specs()):
        raise ValueError('complete regional storage source')
    return dict(kind='signed_storage_increment', child=copy.deepcopy(blocks['full_child']),
                parent=copy.deepcopy(blocks['full_parent']), child_multiplier='1', parent_multiplier='-4')

def build(program, X, **limits):
    out = BASE.build(program, X, **limits)
    out.update(storage_blocks=storage_transport(out['gram_blocks']),
               gram_specs=gram_specs(), gram_program=copy.deepcopy(SPEC))
    return out

def build_blocks(X, **limits):
    out = BASE.build_blocks(X, **limits)
    out.update(storage_blocks=storage_transport(out['blocks']), gram_specs=gram_specs())
    return out

def auxiliary():
    out = BASE.auxiliary()
    out.update(storage_blocks=storage_transport(out['gram_blocks']), gram_specs=gram_specs())
    return out

def anchored_matrix(K, **limits):
    P.ldlt_psd(K, **limits)
    if len(K) != 14:
        raise ValueError('full14 K')
    R = [[F(q) for q in row] for row in K]
    R[0][0] += 1
    return [[str(q) for q in row] for row in R]

def embed_base_grams(grams):
    if type(grams) is not dict or set(grams) != set(BASE.gram_specs()):
        raise ValueError('both original regional matrices')
    out = copy.deepcopy(grams)
    out['storage_K'] = [['0']*14 for _ in range(14)]
    return out

def scalar_budget(grams, X):
    if type(grams) is not dict or set(grams) != set(gram_specs()):
        raise ValueError('complete anchored Gram dictionary')
    out = BASE.scalar_budget({k:grams[k] for k in BASE.gram_specs()}, X)
    K = [[F(q) for q in row] for row in grams['storage_K']]
    if len(K) != 14 or any(len(row) != 14 for row in K) or any(K[i][j] != K[j][i] for i in range(14) for j in range(14)):
        raise ValueError('symmetric full14 storage matrix')
    zKz = sum((K[i][j] for i in range(5,14) for j in range(5,14)), F(0))/4
    charge = -2*X*zKz
    out['ledger'].append(dict(group='storage_K', contribution=str(charge), kind='signed_storage_increment'))
    out.update(total=str(F(out['total'])+charge), storage_zKz=str(zKz),
               storage_contribution=str(charge), storage_is_nonnegative_SOS=False,
               scope='formal exact constant extraction; fixed-matrix O(X), conditional necessary gate', **FLAGS)
    return out
