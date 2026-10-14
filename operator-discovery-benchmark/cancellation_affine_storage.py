"""Full fifteen-dimensional affine completion of signed anchored storage.

The unit is a genuine atom in every regional and storage state. Its actual
initial value and formal scalar extraction are deliberately recorded apart.
"""
from fractions import Fraction as F
import copy
import cancellation_complete_gram_program as BASE
import cancellation_anchored_storage as OLD
import cancellation_shared_gram_language as P
import grouped_arithmetic_language as L

C = BASE.C
FLAGS = dict(global_bound_proved=False, RH_proved=False)
SPEC = dict(version='affine-anchored-full15-storage-v1', base_program=BASE.SPEC,
            atoms=['unit'] + copy.deepcopy(BASE.SPEC['atoms']), dimension=15,
            anchor='prefix', anchor_index=1,
            storage_matrix='R=e_prefix e_prefix^T+K; K PSD',
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


def group_descriptors():
    return {name: dict(kind='complete_affine_arithmetic', region=region, dimension=15,
                       atoms=copy.deepcopy(SPEC['atoms']), normalizer='unit_constant')
            for name, region in [('full_child','child'), ('full_parent','parent')]}


def affine_blocks(blocks):
    if type(blocks) is not dict or set(blocks) != set(BASE.gram_specs()):
        raise ValueError('complete original regional blocks')
    out = {}
    for name, rows in blocks.items():
        if type(rows) is not list or any(type(row) is not list or len(row) != 14 for row in rows):
            raise ValueError('full14 regional source rows')
        out[name] = [[L.dump_poly({():F(1)})]+copy.deepcopy(row) for row in rows]
    return out


def storage_transport(blocks):
    if type(blocks) is not dict or set(blocks) != set(BASE.gram_specs()):
        raise ValueError('complete affine regional storage source')
    if any(type(rows) is not list or any(type(row) is not list or len(row) != 15 for row in rows) for rows in blocks.values()):
        raise ValueError('full15 storage source rows')
    return dict(kind='signed_storage_increment', child=copy.deepcopy(blocks['full_child']),
                parent=copy.deepcopy(blocks['full_parent']), child_multiplier='1', parent_multiplier='-4')


def _archive(X, blocks):
    return {name:dict(descriptor=desc,
                      scales=list(range(2*X,4*X) if desc['region']=='child' else range(X,2*X)),
                      blocks_sha256=C.digest(blocks[name]), block_count=len(blocks[name]), complete_source=True)
            for name,desc in group_descriptors().items()}


def build(program, X, **limits):
    out = BASE.build(program, X, **limits)
    blocks = affine_blocks(out['gram_blocks'])
    out.update(gram_blocks=blocks, gram_archive=_archive(X,blocks), storage_blocks=storage_transport(blocks),
               gram_specs=gram_specs(), gram_program=copy.deepcopy(SPEC))
    return out


def build_blocks(X, **limits):
    out = BASE.build_blocks(X, **limits)
    blocks = affine_blocks(out['blocks'])
    out.update(blocks=blocks, archive=_archive(X,blocks), storage_blocks=storage_transport(blocks), gram_specs=gram_specs())
    return out


def auxiliary():
    out = BASE.auxiliary()
    out.update(storage_blocks=storage_transport(out['gram_blocks']), gram_specs=gram_specs())
    return out


def _matrix(matrix):
    if type(matrix) is not list or len(matrix)!=15 or any(type(row) is not list or len(row)!=15 for row in matrix):
        raise ValueError('full15 matrix dimensions')
    out=[[F(q) for q in row] for row in matrix]
    if any(out[i][j]!=out[j][i] for i in range(15) for j in range(15)):
        raise ValueError('symmetric full15 matrix')
    return out


def anchored_matrix(K, **limits):
    R=_matrix(K)
    P.ldlt_psd(K, **limits)
    R[1][1]+=1
    return [[str(q) for q in row] for row in R]


def _embed(matrix):
    if type(matrix) is not list or len(matrix)!=14 or any(type(row) is not list or len(row)!=14 for row in matrix):
        raise ValueError('original full14 matrix')
    return [['0']*15]+[['0']+copy.deepcopy(row) for row in matrix]


def embed_base_grams(grams):
    if type(grams) is not dict or set(grams)!=set(BASE.gram_specs()):
        raise ValueError('both original regional matrices')
    return {**{name:_embed(matrix) for name,matrix in grams.items()}, 'storage_K':[['0']*15 for _ in range(15)]}


def embed_anchored_grams(grams):
    if type(grams) is not dict or set(grams)!=set(OLD.gram_specs()):
        raise ValueError('complete original anchored matrices')
    return {name:_embed(matrix) for name,matrix in grams.items()}


def quadratic(matrix, vector):
    return sum((vector[i]*matrix[i][j]*vector[j] for i in range(15) for j in range(15)), F(0))


def initial_cost(K, **limits):
    matrix=_matrix(K)
    P.ldlt_psd(K, **limits)
    v=list(map(F,SPEC['actual_initial_vector']))
    cost=1+quadratic(matrix,v)
    return dict(initial_scale=1, unit_state=list(SPEC['actual_initial_vector']), S_R_1=str(cost), E_1='1', initial_cost_finite=True,
                actual_initial_vector=list(SPEC['actual_initial_vector']), storage_initial_cost=str(cost-1),
                anchored_initial_cost=str(cost), formal_vector_is_initial_state=False, **FLAGS)


def scalar_budget(grams, X):
    if type(X) is not int or X<1 or type(grams) is not dict or set(grams)!=set(gram_specs()):
        raise ValueError('complete affine Gram dictionary and positive scale')
    z=list(map(F,SPEC['constant_vector']));ledger=[];values={}
    for name in gram_specs():
        value=quadratic(_matrix(grams[name]),z); values[name]=value
        factor={'full_child':2,'full_parent':1,'storage_K':-2}[name]
        row=dict(group=name,contribution=str(factor*X*value))
        if name=='storage_K':row['kind']='signed_storage_increment'
        ledger.append(row)
    return dict(total=str(sum((F(row['contribution']) for row in ledger),F(0))),ledger=ledger,
                storage_zKz=str(values['storage_K']),storage_contribution=ledger[-1]['contribution'],
                formal_constant_vector=list(SPEC['constant_vector']),storage_is_nonnegative_SOS=False,
                PSD_verified=False,scope='formal exact constant extraction; fixed-matrix O(X), conditional necessary gate',**FLAGS)
