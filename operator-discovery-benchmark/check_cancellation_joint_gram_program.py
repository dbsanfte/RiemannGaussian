"""Independent complete ten-atom regional Gram semantic and scalar audit."""
from fractions import Fraction as F
import copy
import check_cancellation_cell_gram_program as B
import check_cancellation_shared_gram as I
P=B.P
CHANNELS=[dict(theta=t,power=j) for t in ['1/3','1/2','2/3'] for j in [-1,0,1]]
FLAGS=dict(global_bound_proved=False,RH_proved=False)

SPEC=dict(version='joint-divisor-grams-v1',scalar_language=B.C.SPEC,
 legacy_atoms=['prefix','half','even','mod3one','prime'],joint_atoms=['prefix']+copy.deepcopy(CHANNELS),
 regions=['parent','child'],thetas=['1/3','1/2','2/3'],powers=[-1,0,1],
 matrix_sharing='one exact PSD matrix per group, shared across every t and X',
 joint_constant_vector=['0']+['-1/2']*9,auxiliary_blocks='empty for every Gram group')

def group_descriptors():
    groups={}
    for region in SPEC['regions']:
        groups['old_'+region]=dict(kind='legacy',region=region,dimension=5,atoms=SPEC['legacy_atoms'])
        groups['joint_'+region]=dict(kind='joint_divisor_cells',region=region,dimension=10,atoms=SPEC['joint_atoms'],normalizer='unit_constant')
    return {k:copy.deepcopy(groups[k]) for k in sorted(groups)}

def gram_specs():return dict(joint_child=10,joint_parent=10,old_child=5,old_parent=5)

def assemble_blocks(X,old):
    if type(old)is not dict or set(old)!=set(B.gram_specs()):raise ValueError('complete independent pair blocks')
    out={}
    for region in ['parent','child']:
        names=[n for n,d in B.group_descriptors().items() if d['kind']=='divisor_cell' and d['region']==region]
        out['joint_'+region]=[[old[names[0]][i][0]]+[old[n][i][1] for n in names] for i in range(X*(1 if region=='parent' else 2))]
        out['old_'+region]=old['old_'+region]
    out={k:out[k] for k in sorted(out)}
    archive={k:dict(descriptor=group_descriptors()[k],scales=list(range(X,2*X) if k.endswith('parent') else range(2*X,4*X)),blocks_sha256=B.C.digest(v),block_count=len(v),complete_source=True) for k,v in out.items()}
    return dict(blocks=out,archive=archive,gram_specs=gram_specs(),**FLAGS)

def build_blocks(X,**limits):
    return assemble_blocks(X,B.build_blocks(X,**limits)['blocks'])

def build(program,X,**limits):
    out=B.build(program,X,**limits);blocks=assemble_blocks(X,out['gram_blocks'])
    out.update(gram_blocks=blocks['blocks'],gram_archive=blocks['archive'],gram_specs=gram_specs(),gram_program=SPEC)
    return out

def auxiliary():
    out=B.auxiliary();out.update(gram_blocks={k:[] for k in gram_specs()},gram_specs=gram_specs());return out

def check_builder(program,X,out,**limits):
    expected=build(program,X,**limits);ignored={'construction_operations','gram_program_operations','cell_construction_operations','construction_cost'}
    if set(out)-ignored!=set(expected)-ignored:raise ValueError('full builder fields')
    for k in set(expected)-ignored:
        if B.C.digest(out[k])!=B.C.digest(expected[k]):raise ValueError('complete joint semantic mismatch '+k)
    return dict(verified=True,complete_Gram_sources_verified=True,producer_operation_count_independently_verified=False,**FLAGS)

def embed_pair_grams(grams):
    """Sum congruence embeddings; shared prefix diagonal is summed exactly."""
    specs=B.gram_specs()
    if type(grams)is not dict or set(grams)!=set(specs):raise ValueError('complete pair dictionary')
    for name,n in specs.items():
        if type(grams[name])is not list or len(grams[name])!=n:raise ValueError('declared pair dimension')
        I.verify_psd(grams[name])
    out={}
    for region in ['parent','child']:
        names=[n for n,d in B.group_descriptors().items() if d['kind']=='divisor_cell' and d['region']==region]
        matrix=[[F(0)]*10 for _ in range(10)]
        for j,n in enumerate(names,1):
            a=grams[n]
            if len(a)!=2:raise ValueError('pair dimensions')
            I.verify_psd(a)
            for r,s in [(0,0),(0,1),(1,0),(1,1)]:matrix[0 if r==0 else j][0 if s==0 else j]+=F(a[r][s])
        I.verify_psd(matrix);out['joint_'+region]=[[str(q) for q in row] for row in matrix]
        I.verify_psd(grams['old_'+region]);out['old_'+region]=copy.deepcopy(grams['old_'+region])
    return {k:out[k] for k in sorted(out)}

def scalar_budget(grams,X):
    if type(X)is not int or X<1 or type(grams)is not dict or set(grams)!=set(gram_specs()):raise ValueError('complete joint dictionary/scale')
    ledger=[]
    for name,n in gram_specs().items():
        matrix=grams[name]
        if len(matrix)!=n:raise ValueError('joint dimensions')
        I.verify_psd(matrix)
        charge=F(0)
        if name.startswith('joint_'):
            charge=F(X*(1 if name.endswith('parent') else 2),4)*sum((F(matrix[i][j]) for i in range(1,10) for j in range(1,10)),F(0))
        if charge<0:raise ValueError('PSD scalar charge')
        ledger.append(dict(group=name,contribution=str(charge)))
    total=sum((F(r['contribution']) for r in ledger),F(0))
    return dict(total=str(total),linear_coefficient=str(total/X),ledger=ledger,PSD_verified=True,**FLAGS)
