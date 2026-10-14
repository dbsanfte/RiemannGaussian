"""Independent full fourteen-atom regional Gram semantics and embedding."""
from fractions import Fraction as F
import copy
import check_cancellation_joint_gram_program as B
import check_cancellation_shared_gram as I
P=B.P
FLAGS=dict(global_bound_proved=False,RH_proved=False)
SPEC=dict(version='complete-regional-grams-v1',scalar_language=B.B.C.SPEC,
 atoms=copy.deepcopy(B.SPEC['legacy_atoms']+B.SPEC['joint_atoms'][1:]),
 regions=['parent','child'],dimension=14,
 matrix_sharing='one exact PSD matrix per region, shared across every t and X',
 constant_vector=['0']*5+['-1/2']*9,
 selection='union of every prior regional atom; identify shared prefix; retain every pair',
 auxiliary_blocks='empty for every Gram group')
def group_descriptors():
    return {name:dict(kind='complete_arithmetic',region=region,dimension=14,atoms=copy.deepcopy(SPEC['atoms']),normalizer='unit_constant') for name,region in [('full_child','child'),('full_parent','parent')]}

def gram_specs():return dict(full_child=14,full_parent=14)
def assemble_blocks(X,old):
    if type(old)is not dict or set(old)!=set(B.gram_specs()):raise ValueError('complete prior four block groups')
    blocks={};archive={}
    for region in ['child','parent']:
        name='full_'+region;joint=old['joint_'+region];legacy=old['old_'+region]
        count=X*(1 if region=='parent' else 2)
        if len(joint)!=count or len(legacy)!=count:raise ValueError('complete block count')
        rows=[]
        for a,b in zip(legacy,joint):
            if len(a)!=5 or len(b)!=10 or a[0]!=b[0]:raise ValueError('ordered atoms and shared prefix')
            rows.append(copy.deepcopy(a+b[1:]))
        blocks[name]=rows;archive[name]=dict(descriptor=group_descriptors()[name],scales=list(range(X,2*X) if region=='parent' else range(2*X,4*X)),blocks_sha256=B.B.C.digest(rows),block_count=count,complete_source=True)
    return dict(blocks=blocks,archive=archive,gram_specs=gram_specs(),**FLAGS)
def build_blocks(X,**limits):return assemble_blocks(X,B.build_blocks(X,**limits)['blocks'])
def build(program,X,**limits):
    out=B.build(program,X,**limits);data=assemble_blocks(X,out['gram_blocks']);out.update(gram_blocks=data['blocks'],gram_archive=data['archive'],gram_specs=gram_specs(),gram_program=SPEC);return out
def auxiliary():
    out=B.auxiliary();out.update(gram_blocks={k:[] for k in gram_specs()},gram_specs=gram_specs());return out
def check_builder(program,X,out,**limits):
    expected=build(program,X,**limits);ignored={'construction_operations','gram_program_operations','cell_construction_operations','construction_cost'}
    if set(out)-ignored!=set(expected)-ignored:raise ValueError('complete builder fields')
    for k in set(expected)-ignored:
        if B.B.C.digest(out[k])!=B.B.C.digest(expected[k]):raise ValueError('complete fourteen atom semantics '+k)
    return dict(verified=True,complete_Gram_sources_verified=True,producer_operation_count_independently_verified=False,**FLAGS)
def embed_joint_grams(grams):
    if type(grams)is not dict or set(grams)!=set(B.gram_specs()):raise ValueError('complete four Gram matrices')
    for key,n in B.gram_specs().items():
        if len(grams[key])!=n:raise ValueError('declared prior dimension')
        I.verify_psd(grams[key])
    out={}
    for region in ['child','parent']:
        a=[[F(0)]*14 for _ in range(14)]
        for key,ids in [('old_'+region,list(range(5))),('joint_'+region,[0]+list(range(5,14)))]:
            for i,u in enumerate(ids):
                for j,v in enumerate(ids):a[u][v]+=F(grams[key][i][j])
        I.verify_psd(a);out['full_'+region]=[[str(q) for q in row] for row in a]
    return out
def scalar_budget(grams,X):
    if type(X)is not int or X<1 or type(grams)is not dict or set(grams)!=set(gram_specs()):raise ValueError('complete matrix scale')
    ledger=[]
    for key,n in gram_specs().items():
        if len(grams[key])!=n:raise ValueError('full dimension')
        I.verify_psd(grams[key]);charge=F(X*(1 if key.endswith('parent') else 2),4)*sum((F(grams[key][i][j]) for i in range(5,14) for j in range(5,14)),F(0));ledger.append(dict(group=key,contribution=str(charge)))
    total=sum((F(r['contribution']) for r in ledger),F(0))
    return dict(total=str(total),linear_coefficient=str(total/X),ledger=ledger,PSD_verified=True,**FLAGS)
