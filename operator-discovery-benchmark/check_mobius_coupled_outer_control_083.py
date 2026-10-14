"""Independent all-scale whole OUTER BLOCK coupled-control theorem083.
No producer, source signs, sieve, LP or finite science queries. Full remaining
kernel/source growth remains unpaid. Reuses independent083 strict parser/T.
"""
from fractions import Fraction as Q
import json
import check_mobius_coupled_completion_083 as C
from check_mobius_prime_storage_073 import AdmissionError,ResourceLimit,_add,_mul,_rational
class Meter(C.Meter):pass

def _outer(weight):
    kind=weight['kind']
    if kind=='one':return Q(1)
    if kind=='source':return Q(-int(weight['i']==0))
    if kind=='product':return Q(int(weight['i']==weight['j']==0))
    l,r=weight['left'],weight['right']
    if l<=Q(1,5) and r>=Q(1,4):return Q(1)
    if r<=Q(1,5)or l>=Q(1,4):return Q(0)
    raise AdmissionError('band not constant on complete outer interval')
def _saved_weight(weight):return {k:str(v)if isinstance(v,Q)else v for k,v in weight.items()}
def _finish(out,m,error=None):
    if error is not None:out.update(status='INVALID',reason=str(error),resource_limit=isinstance(error,ResourceLimit))
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_growth_proved=False,uniform_full_completion_price_proved=False,uniform_original_source_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,full_remaining_kernel_unpaid=True,source_kernel_binding_still_required=True)
    return out

def _system(program,m):
    p=C.parse_program(program,m)
    # This generic sufficient endpoint binding covers both exact original kernels.
    # Historical source compilation/admission remains separately mandatory.
    if p['kernel'][0]!=(4,Q(-1)):raise AdmissionError('outer source geometry requires minimum divisor4,coefficient-1')
    H00=C.D.drift_matrix(p,m)[0][0];dim=p['memory']+1;terms=p['coupled_terms'];width=len(terms)+dim;groups={};zeros=[]
    m.reserve(16384+(1+len(terms))**2*4096);m.charge((1+len(terms))**2*100)
    for i,term in enumerate(terms):
        weight=term['weight'];value=_outer(weight)
        if not value:zeros.append(i);continue
        cut=term['cut']
        if not(cut['unit_balance']and cut['scale']==1 and cut['n_exponent']==1 and cut['u_exponent']==0):raise AdmissionError('all nonzero outer weights require balanced exact n/complement cuts')
        saved=_saved_weight(weight);key=json.dumps(saved,sort_keys=True,separators=(',',':'))
        if key not in groups:groups[key]=dict(weight=saved,outer_value=str(value),normal_indices=[],complement_indices=[])
        groups[key]['complement_indices'if cut['complement']else 'normal_indices'].append(i)
    ordered=[groups[k]for k in sorted(groups)];rows=[];rhs=[]
    for group in ordered:
        row=[Q(0)]*width
        for i in group['normal_indices']:row[i]=_add(row[i],Q(1),m)
        for i in group['complement_indices']:row[i]=_add(row[i],Q(-1),m)
        rows.append(row);rhs.append(Q(0))
    for arithmetic in ['prime','composite']:
        row=[Q(0)]*width
        for group in ordered:
            if group['weight']['arithmetic']in ['all',arithmetic]:
                for i in group['normal_indices']:row[i]=_add(row[i],Q(group['outer_value']),m)
        row[len(terms)]=Q(-2);rows.append(row);rhs.append(_mul(Q(2),H00,m))
    return p,H00,ordered,zeros,rows,rhs

def equality_constraints(program,meter=None):
    m=meter or Meter();out={}
    try:
        p,H00,groups,zeros,rows,rhs=_system(program,m)
        out.update(status='OUTER_EQUALITY_SYSTEM',parameter_order='theta_then_source_grams',rows=[list(map(str,row))for row in rows],rhs=list(map(str,rhs)),matched_groups=groups,zero_outer_terms=zeros,H00=str(H00),independent_uniform_admission_required=True,source_outer_geometry_verified=True)
    except (ValueError,TypeError,KeyError,OverflowError)as e:return _finish(out,m,e)
    return _finish(out,m)

def verify_certificate(program,certificate,meter=None):
    m=meter or Meter();out={}
    try:
        p,H00,groups,zeros,rows,rhs=_system(program,m)
        keys={'schema','Astar','prime_gain','composite_gain','matched_groups','zero_outer_terms','uniform_bound_coefficient','minimum_u','complete_outer_block_admitted','full_remaining_kernel_unpaid'}
        if type(certificate)is not dict or set(certificate)!=keys or certificate['schema']!='coupled-outer-control-v1':raise AdmissionError('exact whole outer certificate schema')
        if type(certificate['minimum_u'])is not int or certificate['minimum_u']!=1:raise AdmissionError('uniform minimum_u must be integer1')
        if certificate['complete_outer_block_admitted']is not True or certificate['full_remaining_kernel_unpaid']is not True:raise AdmissionError('outer scope flags mandatory true')
        values=[term['theta']for term in p['coupled_terms']]+list(p['gram_weights'])
        for row,target in zip(rows,rhs):
            value=Q(0)
            for a,b in zip(row,values):value=_add(value,_mul(a,b,m),m)
            if value!=target:raise AdmissionError('whole outer exact match/gain equality failed')
        Astar=_add(H00,p['gram_weights'][0],m);gains={'prime':Q(0),'composite':Q(0)};complete=[]
        for group in groups:
            total=Q(0)
            for i in group['normal_indices']:total=_add(total,values[i],m)
            complete.append(dict(group,theta_total=str(total)))
            for arithmetic in gains:
                if group['weight']['arithmetic']in ['all',arithmetic]:gains[arithmetic]=_add(gains[arithmetic],_mul(total,Q(group['outer_value']),m),m)
        for field,value in [('Astar',Astar),('prime_gain',gains['prime']),('composite_gain',gains['composite']),('uniform_bound_coefficient',Astar)]:
            if _rational(certificate[field],field,m)!=value:raise AdmissionError('independent outer '+field+' mismatch')
        supplied=certificate['matched_groups']
        if type(supplied)is not list or len(supplied)!=len(complete):raise AdmissionError('complete matched group array required')
        for group in supplied:
            if type(group)is not dict or set(group)!={'weight','outer_value','normal_indices','complement_indices','theta_total'}:raise AdmissionError('matched group exact schema')
            for key in ['normal_indices','complement_indices']:
                if type(group[key])is not list or len(group[key])>len(p['coupled_terms']) or any(type(i)is not int for i in group[key]):raise AdmissionError('group indices integers,not bool')
            if type(group['weight'])is not dict or len(group['weight'])>4 or any(k in group['weight']and type(group['weight'][k])is not int for k in ['i','j']):raise AdmissionError('group source indices must be integers')
            _rational(group['outer_value'],'outer value',m);_rational(group['theta_total'],'theta total',m)
        if supplied!=complete:raise AdmissionError('complete matched groups/value/total mismatch')
        if type(certificate['zero_outer_terms'])is not list or len(certificate['zero_outer_terms'])>len(p['coupled_terms']) or any(type(i)is not int for i in certificate['zero_outer_terms'])or certificate['zero_outer_terms']!=zeros:raise AdmissionError('complete zero outer term indices mismatch')
        if gains['prime']!=2*Astar or gains['composite']!=2*Astar or Astar<=0:raise AdmissionError('both arithmetic classes require exact2Astar')
        out.update(status='VERIFIED_UNIFORM_WHOLE_OUTER_CONTROL',Astar=str(Astar),prime_gain=str(gains['prime']),composite_gain=str(gains['composite']),uniform_bound_coefficient=str(Astar),minimum_u=1,uniform_whole_outer_absolute_price_proved=True,complete_outer_block_admitted=True,source_outer_geometry_verified=True,matched_groups=complete,zero_outer_terms=zeros,large_u_outer_price='trace(A_outer)+2sum|offdiag|<=3*Astar*N+4*Astar<=Astar*u for integeru>=16',large_u_entries='offdiag Astar*(2-1[m=N]-1[n=N])/(N-1); diag Astar*(1+2*(1-1[n=N])/(N-1))',tiny_u_proof='For1<=u<=15 the outer interval has at most one integer,n=N. Paired balanced cuts both give zero at this diagonal, so price is0 orAstar<=Astar*u. Unitu4 included.',outer_interval='u/5<n<=u/4,all squarefree indices',source_binding_scope='Generic sufficient coefficient geometry min_divisor4 andweight4=-1; actual historical source compilation admission external',whole_program_closure_verified=True)
    except (ValueError,TypeError,KeyError,OverflowError)as e:return _finish(out,m,e)
    return _finish(out,m)
verify_outer_control=verify_certificate
