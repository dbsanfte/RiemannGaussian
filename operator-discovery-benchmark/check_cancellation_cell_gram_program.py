"""Independent complete semantic replay of prefix/divisor shared Gram blocks."""
from fractions import Fraction as F
import copy
import check_cancellation_divisor_cells as C
import check_cancellation_gram as OLD
P=C.P
SPEC=dict(version='cell-shared-grams-v1',scalar_language=C.SPEC,
 legacy_atoms=['prefix','half','even','mod3one','prime'],cell_atoms=['prefix','divisor_contrast'],
 regions=['parent','child'],thetas=['1/3','1/2','2/3'],powers=[-1,0,1],
 matrix_sharing='one exact PSD matrix per group, shared across every t and X',
 cell_constant_vector=['0','-1/2'],auxiliary_blocks='empty for every Gram group')

def group_descriptors():
    groups={'old_'+r:dict(kind='legacy',region=r,dimension=5,atoms=SPEC['legacy_atoms']) for r in SPEC['regions']}
    i=0
    for region in SPEC['regions']:
        for theta in SPEC['thetas']:
            for power in SPEC['powers']:
                groups[f'cell_{i:03d}']=dict(kind='divisor_cell',region=region,theta=theta,power=power,dimension=2,atoms=SPEC['cell_atoms'],normalizer='unit_constant');i+=1
    return {k:copy.deepcopy(groups[k]) for k in sorted(groups)}

def gram_specs():return {k:d['dimension'] for k,d in group_descriptors().items()}

def build_blocks(X,*,max_horizon=80,max_operations=200000000,max_terms=100000,max_coefficient_bits=4096):
    for v in (X,max_horizon,max_operations,max_terms,max_coefficient_bits):
        if type(v)is not int or v<1:raise ValueError('strict positive limits')
    if 4*X-1>max_horizon or 18*(4*X)**2>max_operations:raise OverflowError('complete source preflight')
    old=OLD.atom_blocks(X);blocks={};archive={}
    for name,d in group_descriptors().items():
        ts=list(range(X,2*X) if d['region']=='parent' else range(2*X,4*X));out=[]
        if d['kind']=='legacy':out=old[d['region']]
        else:
            for t in ts:
                r=C.core(t,[str(F(a)**d['power']) for a in range(1,t+1)],dict(kind='divisor_le',coefficient='1',power=d['theta']),max_coefficient_bits)
                out.append([P.canonical(r['P']),P.canonical(r['D'])])
        if any(len(poly)>max_terms for row in out for poly in row):raise OverflowError('atom terms')
        blocks[name]=out;archive[name]=dict(descriptor=d,scales=ts,blocks_sha256=C.digest(out),block_count=len(out),complete_source=True)
    return dict(blocks=blocks,archive=archive,gram_specs=gram_specs(),global_bound_proved=False,RH_proved=False)

def build(program,X,**limits):
    out=C.build(program,X,**limits);b=build_blocks(X,**limits)
    out.update(extension_scope='balanced generic finite dictionary; original lhs and all original groups retained',factor_extension_scope='supplied complete factor/coprime closure; no signed estimate; full target preserved',global_bound_proved=False)
    out.update(gram_blocks=b['blocks'],gram_archive=b['archive'],gram_specs=gram_specs(),gram_program=SPEC)
    return out

def auxiliary():
    out=C.auxiliary();out.update(encoding='explicit auxiliary shared-weight constraint gamma=0; not arithmetic data or same-group semantic observation',scope='necessary gate only for fixed mu templates at q>1 under proved scalar-asymptotic assumptions',requires_target='mu',requires_q_greater_than=1,global_bound_proved=False,RH_proved=False);out.update(gram_blocks={k:[] for k in gram_specs()},gram_specs=gram_specs());return out

def check_builder(program,X,out,**limits):
    expected=build(program,X,**limits)
    ignored={'construction_operations','gram_program_operations','cell_construction_operations','construction_cost'}
    if set(out)-ignored!=set(expected)-ignored:raise ValueError('full builder fields')
    for k in set(expected)-ignored:
        if C.digest(out[k])!=C.digest(expected[k]):raise ValueError('complete semantic builder mismatch '+k)
    return dict(verified=True,complete_Gram_sources_verified=True,producer_operation_count_independently_verified=False,global_bound_proved=False,RH_proved=False)
