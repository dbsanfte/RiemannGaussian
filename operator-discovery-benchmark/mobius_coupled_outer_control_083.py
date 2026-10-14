"""Detector-side symbolic whole-outer proof constraints, without coefficient seeds.
No source signs/sieve or evaluated physical-coordinate data are used.
"""
from fractions import Fraction as Q
import json
import mobius_coupled_completion_083 as S


def _outer_value(weight):
    kind=weight['kind']
    if kind=='one':return Q(1)
    if kind=='source':return Q(-1 if weight['i']==0 else 0)
    if kind=='product':return Q(int(weight['i']==weight['j']==0))
    left,right=Q(weight['left']),Q(weight['right'])
    if left<=Q(1,5) and right>=Q(1,4):return Q(1)
    if right<=Q(1,5) or left>=Q(1,4):return Q(0)
    raise ValueError('band is not constant on whole outer interval')


def equality_constraints(program,meter=None):
    m=meter or S.Meter();out={}
    try:
        p=S.parse_program(program)
        base=[(4,Q(-1)),(5,Q(1)),(8,Q(1)),(10,Q(-1))]
        extended=sorted(base+[(12,Q(-3547,8192)),(15,Q(3547,8192)),(24,Q(3547,8192)),(30,Q(-3547,8192))])
        if p['kernel'] not in (base,extended):raise ValueError('original unfolded kernel binding required')
        H00=S.OLD.drift_matrix(p,m)[0][0]
        groups={};zeros=[];terms=p['coupled_terms'];dim=p['memory']+1;width=len(terms)+dim
        m.reserve(16384+4096*(1+len(terms))**2);m.charge(100*(1+len(terms))**2)
        for i,term in enumerate(terms):
            w=term['weight'];value=_outer_value(w)
            if not value:zeros.append(i);continue
            cut=term['cut']
            if not (cut['unit_balance'] and cut['scale']==1 and cut['n_exponent']==1 and cut['u_exponent']==0):
                raise ValueError('nonzero outer term must be balanced exact n/complement cut')
            key=json.dumps(w,sort_keys=True,separators=(',',':'))
            if key not in groups:groups[key]=dict(weight=w,outer_value=str(value),normal_indices=[],complement_indices=[])
            groups[key]['complement_indices' if cut['complement'] else 'normal_indices'].append(i)
        groups=[groups[k] for k in sorted(groups)];rows=[];rhs=[]
        for group in groups:
            row=[Q(0)]*width
            for i in group['normal_indices']:row[i]+=1
            for i in group['complement_indices']:row[i]-=1
            rows.append(row);rhs.append(Q(0))
        for cls in ('prime','composite'):
            row=[Q(0)]*width
            for group in groups:
                if group['weight']['arithmetic'] in ('all',cls):
                    for i in group['normal_indices']:row[i]+=Q(group['outer_value'])
            row[len(terms)]=-2;rows.append(row);rhs.append(2*H00)
        out.update(status='OUTER_EQUALITY_SYSTEM',parameter_order='theta_then_source_grams',rows=[list(map(str,r)) for r in rows],rhs=list(map(str,rhs)),matched_groups=groups,zero_outer_terms=zeros,H00=str(H00),independent_uniform_admission_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:out.update(status='REJECTED',reason=str(e))
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_source_bound_proved=False,full_remaining_kernel_unpaid=True,RH_proved=False)
    return out


def synthesize(program,meter=None):
    m=meter or S.Meter();system=equality_constraints(program,m);out={}
    if system['status']!='OUTER_EQUALITY_SYSTEM':return system
    try:
        p=S.parse_program(program);values=[t['theta'] for t in p['coupled_terms']]+list(p['gram_weights'])
        S.OLD.rational_budget(values+[Q(system['H00'])],m,terms=max(1,len(values)))
        for row,rhs in zip(system['rows'],system['rhs']):
            if sum((Q(a)*b for a,b in zip(row,values)),Q(0))!=Q(rhs):raise ValueError('exact whole-outer equality not achieved')
        Astar=Q(system['H00'])+p['gram_weights'][0];groups=[];gains={'prime':Q(0),'composite':Q(0)}
        for group in system['matched_groups']:
            total=sum((values[i] for i in group['normal_indices']),Q(0))
            groups.append(dict(group,theta_total=str(total)))
            for cls in gains:
                if group['weight']['arithmetic'] in ('all',cls):gains[cls]+=total*Q(group['outer_value'])
        certificate=dict(schema='coupled-outer-control-v1',Astar=str(Astar),prime_gain=str(gains['prime']),composite_gain=str(gains['composite']),matched_groups=groups,zero_outer_terms=system['zero_outer_terms'],uniform_bound_coefficient=str(Astar),minimum_u=1,complete_outer_block_admitted=True,full_remaining_kernel_unpaid=True)
        out.update(status='PROPOSED_UNIFORM_WHOLE_OUTER_CONTROL',certificate=certificate,independent_uniform_admission_required=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:out.update(status='REJECTED',reason=str(e))
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_source_bound_proved=False,full_remaining_kernel_unpaid=True,RH_proved=False)
    return out
