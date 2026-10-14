"""Independent sparse PRIMAL audit; never a sparse dual-cone audit.
Zero-weight groups remain hash-bound but their polynomials are not expanded.
Uses only independent arithmetic checker primitives, not producer math.
"""
from fractions import Fraction
import hashlib
import json
import re
import time
import check_grouped_arithmetic as G
P=G.P
FLAGS=dict(global_bound_proved=False,RH_proved=False)

def digest(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()).hexdigest()

def rational(value):
    if type(value)is not str or len(value)>4096 or re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?',value)is None:raise ValueError('canonical bounded rational literal')
    return P.rational(value)

def parse(poly,H):
    if type(poly)is not list:raise ValueError('polynomial list')
    for row in poly:
        if type(row)is not dict or set(row)!={'m','c'}:raise ValueError('polynomial term fields')
        rational(row['c'])
    return P.parse(poly,H)

def verify_joint_result(instances,result,*,allow_constant_slack=False,expected_instance_sha256=None,max_operations=200000000,time_limit=60):
    if type(instances)is not list or not instances:raise ValueError('nonempty instances')
    if type(allow_constant_slack)is not bool or type(max_operations)is not int or max_operations<1 or type(time_limit)not in(int,float)or not 0<time_limit< float('inf'):raise ValueError('resource/flag domain')
    start=time.monotonic();used=0
    def charge(n=1):
        nonlocal used
        used+=n
        if used>max_operations or time.monotonic()-start>time_limit:raise OverflowError('sparse audit work/time')
    if type(result)is not dict:raise ValueError('result dictionary')
    if any(result.get(k) is True for k in ('global_bound_proved','RH_proved','actual_signed_upper_bound_proved')):raise ValueError('global promotion forbidden')
    hashes=[digest(i)for i in instances]
    if expected_instance_sha256 is not None and (type(expected_instance_sha256)is not list or hashes!=expected_instance_sha256):raise ValueError('original source instance hash binding')
    status=result.get('status')
    if status!='finite_certificate':
        if status not in ('no_certificate_found','missing_resource')or 'certificates'in result:raise ValueError('explicit noncertificate result')
        return dict(verified=True,status=status,finite_verified=False,instance_sha256=hashes,**FLAGS)
    weights=result['weights']
    if type(weights)is not dict or set(weights)!={'square_weights','relation_weights'}or any(type(weights[k])is not list for k in weights):raise ValueError('shared weight schema')
    sw=[rational(v)for v in weights['square_weights']];rw=[rational(v)for v in weights['relation_weights']]
    if any(w<0 for w in sw):raise ValueError('negative shared square weight')
    if type(result['certificates'])is not list or len(result['certificates'])!=len(instances):raise ValueError('certificate coverage')
    audits=[];active_squares=active_relations=skipped_groups=0;relation_cache={}
    for inst,cert in zip(instances,result['certificates']):
        if type(inst)is not dict or set(inst)!={'target','horizon','lhs','square_groups','relation_groups'}:raise ValueError('original instance fields')
        H,t=inst['horizon'],inst['target'];P.integer(H);P.guard(H,'horizon')
        if t not in ('mu','c'):raise ValueError('actual target')
        if type(inst['square_groups'])is not list or type(inst['relation_groups'])is not list or len(inst['square_groups'])!=len(sw)or len(inst['relation_groups'])!=len(rw):raise ValueError('shared group dimensions')
        lhs=parse(inst['lhs'],H);rhs={};expected=dict(target=t,horizon=H,lhs=inst['lhs'],squares=[],relations=[])
        for weight,group in zip(sw,inst['square_groups']):
            if type(group)is not list:raise ValueError('square group list')
            if not weight:skipped_groups+=1
            for term in group:
                charge()
                if type(term)is not dict or set(term)!={'weight','poly'}or type(term['poly'])is not list:raise ValueError('square group atom schema')
                own=rational(term['weight'])
                if own<0:raise ValueError('negative within square group')
                p=parse(term['poly'],H);charge(len(p))
                if not weight or not own:continue
                charge(len(p)**2);value=weight*own
                rhs=P.add(rhs,P.multiply(p,p),value);expected['squares'].append(dict(weight=str(value),poly=term['poly']));active_squares+=1
        for weight,group in zip(rw,inst['relation_groups']):
            if type(group)is not list:raise ValueError('relation group list')
            if not weight:skipped_groups+=1
            for term in group:
                charge()
                if type(term)is not dict or set(term)!={'spec','multiplier'}or type(term['spec'])is not dict or type(term['multiplier'])is not list:raise ValueError('relation group atom schema')
                key=(t,H,digest(term['spec']))
                if key not in relation_cache:relation_cache[key]=G.relation(term['spec'],t,H)
                q=relation_cache[key];m=parse(term['multiplier'],H);charge(len(m))
                if not weight:continue
                charge(len(q)*len(m))
                rhs=P.add(rhs,P.multiply(m,q),weight)
                expected['relations'].append(dict(spec=term['spec'],multiplier=P.canonical({a:weight*v for a,v in m.items()})));active_relations+=1
        residue=P.add(lhs,rhs,Fraction(-1))
        if any(m for m in residue):raise ValueError('full original nonconstant residual')
        slack=residue.get((),Fraction(0))
        if slack<0 or (not allow_constant_slack and slack):raise ValueError('constant residual domain')
        if allow_constant_slack and slack:expected['squares'].append(dict(weight=str(slack),poly=[dict(m=[],c='1')]))
        if cert!=expected:raise ValueError('exact expanded certificate binding')
        audits.append(dict(target=t,horizon=H,finite_identity_verified=True,constant_slack=str(slack)))
    if allow_constant_slack and result['constant_slacks']!=[a['constant_slack']for a in audits]:raise ValueError('exact scalar slack binding')
    return dict(verified=True,instances=audits,shared_weights_verified=True,finite_only=True,instance_sha256=hashes,source_binding_checked=expected_instance_sha256 is not None,active_square_atoms=active_squares,active_relation_atoms=active_relations,skipped_zero_groups=skipped_groups,charged_operations=used,elapsed_seconds=time.monotonic()-start,scope='full original primal identity and active arithmetic premises; all source polynomial schemas and arithmetic premises validated; zero groups hash-bound without products; not dual verification',**FLAGS)
