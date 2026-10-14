"""Direct exact checking of a separator for the licensed finite augmented cone.

The designated completed publication028 chart is a prior mathematical premise.
This checker does not replay elimination, LP assembly, numerical optimization or
an eigensolver. Declared rational rank-one vectors are positive generators by
algebra; their numerical eigenvector provenance is not a proof premise.
"""
from fractions import Fraction as F
import json
import time
import check_primitive_state_feedback_affine as EXACT

require=EXACT.require
SCHEMA='primitive-state-chart-dual-independent-check-v1'
CERTIFICATE_SCHEMA='primitive-state-chart-dual-certificate-v1'
RAYS_SCHEMA='primitive-state-chart-dual-rays-v1'
WIDTH=1224
SCALAR_INDICES=[*range(366),*range(979,984)]
C_INDICES=list(range(984,1104))
P_INDICES=list(range(1104,1224))
PAIRS=[(i,j)for i in range(15)for j in range(i,15)]
FLAGS=dict(global_bound_proved=False,RH_proved=False,universal_identity_proved=False,candidate_admitted=False,exact_admission=False,primal_feasibility_proved=False)


def encoded(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


class Budget(EXACT.Budget):
    def __init__(self,deadline,max_operations=50000000,max_cells=6000000,max_bits=4096):
        require(type(max_operations)is int and 0<max_operations<=50000000,'one50m final exact audit')
        super().__init__(deadline,max_operations,max_cells,20000000,max_bits)


def scope_flags(value):
    require(type(value)is dict,'explicit certificate scope')
    for k in FLAGS:require(value.get(k)is False,'finite augmented cone certificate cannot establish '+k)
    for k in ('infeasibility_proved','finite_cone_infeasibility_verified','numerical_infeasibility_admitted'):
        if k in value:require(value[k]is False,'producer cannot pre-admit '+k)


def retained_indices():
    return [*range(366),*[366+2*i for i in range(613)],*range(1592,1837)]


def parse_chart(chart,parent_review,b):
    """Load the designated published span premise, not arbitrary trusted=True."""
    require(parent_review.get('schema')=='primitive-state-augmented-cone-search-independent-review-v1'and parent_review.get('all_passed')is True and parent_review.get('chart_verified')is True and parent_review.get('center_verified')is True and parent_review.get('status')in('SCALAR_REJECTED','CONE_CHECKED'),'completed designated publication028 chart premise')
    check=parent_review.get('independent_search_check');require(type(check)is dict and check.get('verified')is True and check.get('chart_verified')is True and check.get('center_verified')is True and check.get('chart_used_without_old_tape_replay')is True,'prior complete augmented chart proof, not an unchecked numerical result')
    require(chart.get('schema')=='primitive-state-augmented-cone-chart-v1'and chart.get('complete')is True and chart.get('width')==WIDTH and chart.get('original_width')==1957 and chart.get('retained_indices')==retained_indices()and all(type(j)is int for j in chart['retained_indices']),'fixed original1957 quotient1224 layout')
    records=chart.get('normalized_rows');require(type(records)is list and len(records)==782,'all782 stored normalized rows')
    rows=[];pivots=[];previous=-1;cells=0
    for record in records:
        require(type(record)is dict and set(record)=={'pivot','terms'},'explicit complete normalized row')
        p=record['pivot'];require(type(p)is int and previous<p<WIDTH,'ordered unique variable pivots');previous=p
        terms=record['terms'];require(type(terms)is list and 0<len(terms)<=WIDTH+1,'bounded complete sparse row');row={};last=-1
        for term in terms:
            require(type(term)is list and len(term)==2,'exact sparse augmented coefficient');j,text=term;require(type(j)is int and last<j<=WIDTH,'ordered sparse augmented columns');last=j;q=b.rational(text);require(q!=0,'nonzero sparse coefficient');row[j]=q
        require(row.get(p)==1 and min(row)==p,'normalized upper triangular chart')
        rows.append(row);pivots.append(p);cells+=len(row);b.live(cells+3*WIDTH+2*782)
    free=[j for j in range(WIDTH)if j not in pivots]
    require(chart.get('pivot_columns')==pivots and chart.get('free_indices')==free and len(free)==442,'complete782/442 partition')
    old=chart.get('old_pivots');require(type(old)is list and len(old)==780 and all(type(p)is int for p in old)and old==sorted(set(old))and set(old).issubset(pivots)and sorted(set(pivots)-set(old))==[160,170],'prior780 plus two actual learned pivots')
    return rows,pivots,free,cells


def fixed_descriptions():
    records=[]
    for i in SCALAR_INDICES:records.append(dict(index=len(records),kind='scalar',coordinate=i))
    for block in('C','H'):
        for i in range(15):
            v=['0']*15;v[i]='1';records.append(dict(index=len(records),kind='rank_one',block=block,vector=v,origin='axis'))
        for i in range(15):
            for j in range(i+1,15):
                for sign,origin in((1,'pair_plus'),(-1,'pair_minus')):
                    v=['0']*15;v[i]='1';v[j]=str(sign);records.append(dict(index=len(records),kind='rank_one',block=block,vector=v,origin=origin))
    return records


def generator(record,b):
    """Return exact coefficients of a nonnegative scalar or v^T C/H v."""
    if record.get('kind')=='scalar':
        require(set(record)=={'index','kind','coordinate'}and type(record['coordinate'])is int and record['coordinate']in SCALAR_INDICES,'licensed nonnegative scalar ray')
        return {record['coordinate']:F(1)}
    require(record.get('kind')=='rank_one'and set(record)=={'index','kind','block','vector','origin'}and record.get('block')in('C','H'),'explicit C/H rational rank-one generator')
    require(type(record.get('vector'))is list and len(record['vector'])==15,'complete15-dimensional rational vector');v=[b.rational(q)for q in record['vector']];require(any(v),'nonzero ray vector')
    row={};b.charge(len(PAIRS))
    for k,(i,j)in enumerate(PAIRS):
        if not v[i]or not v[j]:continue
        q=b.mul(v[i],v[j])
        if i!=j:q=b.mul(F(2),q)
        if not q:continue
        row[C_INDICES[k]]=q if record['block']=='C'else b.mul(F(4),q)
        if record['block']=='H':row[P_INDICES[k]]=q
    return row


def parse_rays(envelope,b):
    require(type(envelope)is dict and envelope.get('schema')==RAYS_SCHEMA and envelope.get('complete')is True and envelope.get('width')==WIDTH,'complete declared rational generator catalog')
    for k,value in dict(retained_indices=retained_indices(),scalar_projected_indices=SCALAR_INDICES,C_projected_indices=C_INDICES,P_projected_indices=P_INDICES).items():require(envelope.get(k)==value,'fixed quotient generator layout '+k)
    policy=envelope.get('policy')
    if policy is not None:require(type(policy)is dict and policy.get('numerical_eigenvectors_certified')is False,'declared eigenvector provenance remains uncertified')
    records=envelope.get('records');require(type(records)is list and len(records)==851,'821 fixed and30 declared dyadic endpoint directions')
    fixed=fixed_descriptions();b.charge(17*821);require(records[:821]==fixed,'complete deterministic scalar and fixed rank-one catalog; no omissions or reorder')
    generators=[];cells=0
    for index,record in enumerate(records):
        require(type(record)is dict and type(record.get('index'))is int and record['index']==index,'every generator explicitly numbered')
        if index>=821:
            require(record.get('kind')=='rank_one'and record.get('origin')=='endpoint_eigenvector'and record.get('block')==('C'if index<836 else'H'),'all fifteen declared directions for each endpoint block')
            values=record.get('vector');require(type(values)is list and len(values)==15,'complete declared dyadic direction');v=[b.rational(q)for q in values]
            require(any(v)and all(abs(q)<=1 and (1<<20)%q.denominator==0 for q in v),'bounded denominator2^20 dyadic direction')
            require(next(q for q in v if q)>0,'first nonzero vector component has fixed positive sign')
        row=generator(record,b);generators.append(row);cells+=len(row);b.live(cells+3*WIDTH+2*851)
    return generators,cells


def check_identity(rows,generators,alpha,lambdas,width,b):
    """A^T lambda=G alpha and b^T lambda=-1 are checked in every column."""
    require(type(width)is int and 0<width<=WIDTH and len(alpha)==len(generators)and len(lambdas)==len(rows),'complete explicit exact weights')
    alpha=[b.rational(q)for q in alpha];lambdas=[b.rational(q)for q in lambdas];require(all(q>=0 for q in alpha),'nonnegative generator coefficients')
    cone=[F(0)]*width;left=[F(0)]*width;pairing=F(0)
    b.charge(len(generators)+len(rows))
    for a,row in zip(alpha,generators):
        if not a:continue
        for j,q in row.items():require(type(j)is int and 0<=j<width,'generator coordinate');cone[j]=b.add(cone[j],b.mul(a,q))
    for multiplier,row in zip(lambdas,rows):
        if not multiplier:continue
        for j,q in row.items():
            require(type(j)is int and 0<=j<=width,'chart augmented coordinate')
            if j==width:pairing=b.add(pairing,b.mul(multiplier,q))
            else:left[j]=b.add(left[j],b.mul(multiplier,q))
    require(left==cone,'every exact coordinate of A^T lambda equals the cone functional')
    require(pairing==F(-1),'exact negative chart RHS pairing -1')
    return cone,pairing,sum(q>0 for q in alpha),sum(q!=0 for q in lambdas)


def verify_certificate(chart,parent_review,certificate,*,deadline=None,max_operations=50000000,max_cells=6000000,max_bits=4096,max_certificate_bytes=8388608):
    require(type(max_certificate_bytes)is int and 0<max_certificate_bytes<=8388608,'bounded exact witness file')
    b=Budget(time.monotonic()+3600 if deadline is None else deadline,max_operations,max_cells,max_bits)
    try:
        require(type(certificate)is dict,'explicit proposed certificate');data=encoded(certificate)
        if len(data)>max_certificate_bytes:raise OverflowError('exact witness byte cap')
        b.charge(2*(len(data)//64+1),cells=len(data)//64+1);scope_flags(certificate)
        require(certificate.get('schema')==CERTIFICATE_SCHEMA and certificate.get('complete')is True and certificate.get('width')==WIDTH and certificate.get('exact_identity_verified')is True,'complete exact certificate proposed for independent verification')
        rows,pivots,free,source_cells=parse_chart(chart,parent_review,b)
        require(certificate.get('pivot_columns')==pivots and certificate.get('free_indices')==free,'exact chart coordinate partition binding')
        rays,ray_cells=parse_rays(certificate.get('rays'),b)
        alpha=certificate.get('alpha');lambdas=certificate.get('lambda_vector');require(type(alpha)is list and len(alpha)==851 and type(lambdas)is list and len(lambdas)==782,'no implicit missing or zero weights')
        b.live(source_cells+ray_cells+4*WIDTH+2*851+2*782)
        w,pairing,active,multipliers=check_identity(rows,rays,alpha,lambdas,WIDTH,b)
        require(certificate.get('pairing')==str(pairing)and certificate.get('combined_functional')==list(map(str,w)),'full independently recomputed functional and exact negative pairing')
        result=dict(schema=SCHEMA,verified=True,complete=True,status='FINITE_CONE_INFEASIBLE',finite_augmented_cone_infeasibility_certified=True,original_unlearned_cone_infeasibility_certified=False,licensed_chart_used=True,old_elimination_replayed=False,rank=782,free_coordinates=442,generator_count=851,active_generators=active,nonzero_row_multipliers=multipliers,nonnegative_weights_verified=True,all_coordinate_equalities_verified=True,rank_one_cone_generators_verified=True,pairing='-1',native_LP_replayed=False,native_eigenvectors_independently_verified=False,scope='licensed finite augmented equation and cone system including three necessary formal rows only',**FLAGS)
        payload=encoded(result);b.charge(2*(len(payload)//64+1));result.update(audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,independent_audit_work_reserve=b.operations)
        return result
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise


def verify_outcome(chart,parent_review,outcome,**kwargs):
    """A missing witness never certifies infeasibility or primal feasibility."""
    require(type(outcome)is dict and outcome.get('status')in('CERTIFICATE_PROPOSED','NONCERTIFIED','UNKNOWN'),'explicit exact-restoration outcome')
    scope_flags(outcome)
    for key in ('finite_augmented_cone_infeasibility_certified','primal_feasibility_certified','finite_cone_infeasibility_verified','numerical_infeasibility_admitted'):
        if key in outcome:require(outcome[key]is False,'producer cannot certify '+key)
    if outcome['status']=='CERTIFICATE_PROPOSED':return verify_certificate(chart,parent_review,outcome.get('certificate'),**kwargs)
    require(outcome.get('certificate')is None,'unsuccessful outcome has no admitted witness')
    b=Budget(kwargs.get('deadline',time.monotonic()+3600),kwargs.get('max_operations',50000000),kwargs.get('max_cells',6000000),kwargs.get('max_bits',4096))
    try:
        cap=kwargs.get('max_certificate_bytes',8388608);require(type(cap)is int and 0<cap<=8388608,'bounded unsuccessful diagnostic cap')
        data=encoded(outcome)
        if len(data)>cap:raise OverflowError('bounded unsuccessful diagnostic')
        b.charge(2*(len(data)//64+1))
        return dict(schema=SCHEMA,verified=True,complete=False,status=outcome['status'],finite_augmented_cone_infeasibility_certified=False,original_unlearned_cone_infeasibility_certified=False,primal_feasibility_certified=False,native_LP_replayed=False,native_eigenvectors_independently_verified=False,audit_operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells,independent_audit_work_reserve=b.operations,**FLAGS)
    except(OverflowError,TimeoutError,MemoryError)as error:
        error.independent_audit_counts=dict(operations=b.operations,audit_cells=b.audit_cells,peak_live_cells=b.peak_live_cells)
        raise
