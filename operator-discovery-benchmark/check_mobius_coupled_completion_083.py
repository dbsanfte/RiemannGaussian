"""Independent full-squarefree coupled-divisor finite upper/dual checker083.
No producer import, unknown-composite mu signs or observed full-source values.
Optional elementary unit/prime signs are explicitly anchored. Frozen independent082
program/T and squarefree sieve primitives plus073 rational roots are reused.
"""
from fractions import Fraction as Q
from math import gcd
from flint import fmpq_mat
import numpy as np
import check_mobius_dense_completion_082 as D
from check_mobius_prime_storage_073 import (AdmissionError,ResourceLimit,_rational,_add,_mul,_divide,_int_mul,_power_target,_integer_root)
MAX_HORIZON=16384
MAX_COORDINATES=4096
MAX_TERMS=128
class Meter(D.Meter):pass

def floor_cut(scale,n_exponent,u_exponent,n,u,N,meter=None):
    """Exact floor(scale*n^eta*u^beta) capped atN, signed rational exponents."""
    m=meter or Meter();degree=_int_mul(n_exponent.denominator//gcd(n_exponent.denominator,u_exponent.denominator),u_exponent.denominator,m)
    ne=n_exponent.numerator*(degree//n_exponent.denominator);ue=u_exponent.numerator*(degree//u_exponent.denominator)
    numerator=_power_target(scale.numerator,degree,1,0,m);denominator=_power_target(scale.denominator,degree,1,0,m)
    for base,exponent in [(n,ne),(u,ue)]:
        value=_power_target(base,abs(exponent),1,0,m)
        if exponent>=0:numerator=_int_mul(numerator,value,m)
        else:denominator=_int_mul(denominator,value,m)
    return min(N,_integer_root(numerator//denominator,degree,m))

def _finish(out,m,error=None):
    if error is not None:out.update(status='INVALID',reason=str(error),resource_limit=isinstance(error,ResourceLimit))
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_growth_proved=False,uniform_original_source_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,source_kernel_binding_still_required=True,unknown_composite_signs_used=False,observed_full_source_values_used=False)
    return out

def build_model(program,u,meter=None):
    """Raising exact full-coordinate model; never groups or discards SF indices."""
    m=meter or Meter();p=parse_program(program,m);D.integer(u,'u',1,(1<<4096)-1);N=u//p['kernel'][0][0]
    if N>MAX_HORIZON:raise ResourceLimit('full source horizon exceeds16384 before allocation')
    T=D.drift_matrix(p,m);prefix=D.squarefree_prefix(N,m)
    coordinates=tuple(n for n in range(1,N+1)if prefix[n]!=prefix[n-1]);G=len(coordinates)
    if G>MAX_COORDINATES:raise ResourceLimit('full squarefree matrix exceeds4096 coordinates')
    dim=p['memory']+1;features=[];cuts=[];weights=[]
    resident_bytes=_vector_budget(p,N,G,m)
    prime=is_prime_table(N,m)
    for n in coordinates:
        f=[]
        for i in range(dim):
            value=Q(0)
            for d,w in p['kernel']:
                if n<=u//((1<<i)*d):value=_add(value,w,m)
            f.append(value)
        features.append(tuple(f))
    cut_cache={}
    for term in p['coupled_terms']:
        cut=term['cut'];ks=[];ws=[];cut_key=tuple(cut.items());saved=cut_cache.get(cut_key)
        for g,(n,f)in enumerate(zip(coordinates,features)):
            if saved is not None:K=saved[g]
            else:
                K=floor_cut(cut['scale'],cut['n_exponent'],cut['u_exponent'],n,u,N,m)
                if cut['complement']:K=N-K
            ks.append(K);ws.append(weight_value(term['weight'],n,u,N,f,bool(prime[n]),m))
        cut_cache[cut_key]=tuple(ks);cuts.append(cut_cache[cut_key]);weights.append(tuple(ws))
    if p['prime_anchor']and G:
        effective_indices=[];signs=[];labels=['anchor'];known=0
        for n in coordinates:
            if n==1 or prime[n]:effective_indices.append(0);signs.append(1 if n==1 else -1);known+=1
            else:effective_indices.append(len(labels));signs.append(1);labels.append(n)
    else:effective_indices=list(range(G));signs=[1]*G;labels=list(coordinates);known=0
    return dict(program=p,u=u,N=N,coordinates=coordinates,squarefree_count=G,features=tuple(features),cuts=tuple(cuts),weights=tuple(weights),T=T,prime_count=sum(bool(prime[n])for n in coordinates),unit_balance_columns=sum(term['cut']['unit_balance']for term in p['coupled_terms']),resident_bytes=resident_bytes,projection_indices=tuple(effective_indices),projection_signs=tuple(signs),effective_labels=tuple(labels),effective_dimension=len(labels),known_sign_coordinates=known)

def _budget(model,m,extra_values=(),extra_bytes=0):
    p=model['program'];values=[v for row in model['T']for v in row]+[v for row in model['features']for v in row]+[v for row in model['weights']for v in row]+[term['theta']for term in p['coupled_terms']]+list(p['gram_weights'])+list(extra_values)
    common=1;largest=1
    for v in values:
        common=_int_mul(common//gcd(common,v.denominator),v.denominator,m);largest=max(largest,abs(v.numerator).bit_length())
    terms=(p['memory']+1)**2+len(p['coupled_terms'])+len(p['gram_weights'])
    bits=4*(common.bit_length()+largest)+2*max(1,model['N'].bit_length())+max(1,terms.bit_length())+16
    if bits>100000:raise ResourceLimit('prospective full matrix rational bit gate')
    G=model['squarefree_count'];m.reserve(model['resident_bytes']+16384+8*(model['N']+1)+extra_bytes+G*G*(256+bits)+G*(512+bits));m.charge(G*G*max(1,terms))

def _entry(model,g,h,m,theta=True,gram=True):
    p=model['program'];dim=p['memory']+1;x=model['features'][g];y=model['features'][h];a=Q(0)
    for i in range(dim):
        for j in range(dim):
            if model['T'][i][j] and x[i] and y[j]:a=_add(a,_mul(model['T'][i][j],_mul(x[i],y[j],m),m),m)
    if theta:
        for k,term in enumerate(p['coupled_terms']):
            if term['theta']:a=_add(a,_mul(term['theta'],_zentry(model,k,g,h,m),m),m)
    if gram:
        for i,w in enumerate(p['gram_weights']):
            if w and x[i] and y[i]:a=_add(a,_mul(w,_mul(x[i],y[i],m),m),m)
    return a

def _zentry(model,k,g,h,m):
    n=model['coordinates'][g];v=model['coordinates'][h];Kn=model['cuts'][k][g];Kv=model['cuts'][k][h]
    # columnn uses K(n),weight(n), evaluated at rowm; both unit corrections.
    first=_dvalue(model,k,Kv,n,m)
    second=_dvalue(model,k,Kn,v,m)
    return _divide(_add(_mul(model['weights'][k][h],first,m),_mul(model['weights'][k][g],second,m),m),Q(2),m)

def literal_corrected_matrix(model,meter=None):
    m=meter or Meter();_budget(model,m);G=model['squarefree_count'];A=[[Q(0)for _ in range(G)]for _ in range(G)]
    for g in range(G):
        for h in range(g,G):A[g][h]=A[h][g]=_entry(model,g,h,m)
    return A

def _integer_columns(model,k,m):
    """Independent exact integer D numerator, rows m and columns n."""
    N=model['N'];coords=model['coordinates'];ks=model['cuts'][k]
    balance=model['program']['coupled_terms'][k]['cut']['unit_balance']and N>=2
    den=N-1 if balance else 1;G=len(coords)
    m.reserve(model['resident_bytes']+G*G*128);m.charge(G*G*4)
    rows=[]
    for n in coords:
        unit=int(n==1);cn=N//n-unit
        rows.append([den*(K//n-unit if K else 0)-(max(K-1,0)*cn if balance else 0)for K in ks])
    return rows,den

def corrected_matrix(model,meter=None):
    """Native rational contraction; literal_corrected_matrix remains oracle."""
    m=meter or Meter();_budget(model,m);G=model['squarefree_count'];p=model['program']
    if not G:return []
    F=fmpq_mat([[str(v)for v in row]for row in model['features']]);dim=p['memory']+1
    T=fmpq_mat([[str(model['T'][i][j]+(p['gram_weights'][i]if i==j else 0))for j in range(dim)]for i in range(dim)])
    A=F*T*F.transpose();cache={}
    for k,term in enumerate(p['coupled_terms']):
        if not term['theta'] or not any(model['weights'][k]):continue
        key=(model['cuts'][k],term['cut']['unit_balance'])
        # One cached geometry at a time, avoiding unbounded retained matrices.
        if key not in cache:
            cache.clear();rows,den=_integer_columns(model,k,m);cache[key]=(fmpq_mat(rows),den)
        Dm,den=cache[key];w=model['weights'][k]
        wc=1
        for v in w:wc=_int_mul(wc//gcd(wc,v.denominator),v.denominator,m)
        wi=[int(v*wc)for v in w];dbound=max(1,model['N']**2)
        if max((abs(v)for v in wi),default=0)*dbound < (1<<62):
            arr=np.asarray([[int(Dm[i,j])for j in range(G)]for i in range(G)],dtype=np.int64)
            arr*=np.asarray(wi,dtype=np.int64)[None,:]
            weighted=fmpq_mat(arr.tolist())/(den*wc)
        else:
            weighted=fmpq_mat([[int(Dm[i,j])*wi[j]for j in range(G)]for i in range(G)])/(den*wc)
        A+=(weighted+weighted.transpose())*fmpq_mat([[str(term['theta']/2)]])[0,0]
    m.charge(G*G*max(1,len(p['coupled_terms']))*8)
    return [[Q(str(A[i,j]))for j in range(G)]for i in range(G)]

def verify_certificate(program,u,certificate,meter=None):
    m=meter or Meter();out={}
    try:
        model=build_model(program,u,m);G=model['squarefree_count']
        if type(certificate)is not dict or set(certificate)!={'squarefree_count','price','row_prices'}:raise AdmissionError('exact coupled upper certificate schema')
        if type(certificate['squarefree_count'])is not int or certificate['squarefree_count']!=G:raise AdmissionError('complete squarefree count mismatch')
        if type(certificate['row_prices'])is not list or len(certificate['row_prices'])!=model['effective_dimension']:raise AdmissionError('all effective coordinate row prices required')
        supplied=tuple(_rational(v,'row price',m)for v in certificate['row_prices']);price=_rational(certificate['price'],'price',m)
        A=price_matrix(model,m);rows=[]
        for g,row in enumerate(A):
            value=row[g]
            for h,a in enumerate(row):
                if g!=h:value=_add(value,abs(a),m)
            rows.append(value) # Boolean diagonal is FIXED1, never clamp to0.
        total=Q(0)
        for value in rows:total=_add(total,value,m)
        if supplied!=tuple(rows)or price!=total:raise AdmissionError('independent full Boolean-SF price mismatch')
        out.update(status='VERIFIED_FINITE_COUPLED_UPPER_BOUND',u=u,horizon=model['N'],squarefree_count=G,price=str(total),row_prices=list(map(str,rows)),complete_target_admitted=True,prime_edges_retained=True,unit_included=model['N']>=1,coupled_divisor_zero_identities_verified=True,positive_Gram_cost_retained=True,prime_signs_anchored=model['program']['prime_anchor'],known_sign_coordinates=model['known_sign_coordinates'],effective_dimension=model['effective_dimension'],effective_coordinate_order=list(model['effective_labels']),prime_count=model['prime_count'],unit_balance_columns=model['unit_balance_columns'],Boolean_squarefree_diagonals_exact=True,proof='Full squarefree mu diagonals equal1. Optional exact unit/prime signs are jointly collapsed into fixed anchor1; all effective diagonals equal1. Effective quadratic <=trace(Aeff)+2sum_offdiag|Aeff|; complete coupled identities vanish and positive Gram is added.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return _finish(out,m,e)
    return _finish(out,m)

def verify_price_dual(program,u,certificate,meter=None):
    m=meter or Meter();out={}
    try:
        model=build_model(program,u,m);G=model['squarefree_count'];E=model['effective_dimension'];pairs=E*(E-1)//2
        if type(certificate)is not dict or set(certificate)!={'nu','lower_bound'}or type(certificate['nu'])is not list or len(certificate['nu'])!=pairs:raise AdmissionError('exact complete coupled dual shape/schema')
        rawbytes=16384
        for v in certificate['nu']:
            if type(v)is not str:raise AdmissionError('canonical nu strings')
            rawbytes+=512+8*len(v)
        m.reserve(model['resident_bytes']+rawbytes+8*(model['N']+1));nu=tuple(_rational(v,'nu',m)for v in certificate['nu']);supplied=_rational(certificate['lower_bound'],'lower_bound',m)
        if any(abs(v)>2 for v in nu):raise AdmissionError('Boolean price dual nu[-2,2] required')
        _budget(model,m,nu,rawbytes);p=model['program']
        base,zs,grams=_dual_functionals(model,nu,m)
        lower=base
        for z in zs:lower=_add(lower,-_mul(Q(16),abs(z),m),m)
        for z in grams:lower=_add(lower,_mul(Q(16),min(Q(0),z),m),m)
        if supplied!=lower:raise AdmissionError('independent coupled box price dual mismatch')
        out.update(status='VERIFIED_FINITE_COUPLED_PRICE_LOWER_BOUND',u=u,horizon=model['N'],squarefree_count=G,lower_bound=str(lower),base_functional=str(base),coupled_template_functionals=list(map(str,zs)),gram_template_functionals=list(map(str,grams)),diagonal_dual_fixed_one=True,prime_signs_anchored=model['program']['prime_anchor'],known_sign_coordinates=model['known_sign_coordinates'],effective_dimension=E,effective_coordinate_order=list(model['effective_labels']),pair_order='lexicographic effective positions g<h: optional anchor then increasing squarefree composites',actual_parameter_values_irrelevant=True,actual_signed_drift_lower_bound_proved=False,uniform_price_lower_bound_proved=False,proof='Effective Boolean price is trace(Aeff)+2sum|offdiag|; fixed diag1 and feasible nu[-2,2] lift exactly through optional known unit/prime signs into all raw matrix templates, and minimize over the full theta/Gram boxes.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return _finish(out,m,e)
    return _finish(out,m)

def parse_program(raw,meter=None):
    m=meter or Meter();keys={'schema','kernel','memory','rays','drift_multiplier','coupled_terms','gram_weights'}
    if type(raw)is not dict or set(raw)not in (keys,keys|{'prime_anchor'}) or raw['schema']!='coupled-divisor-completion-v1':raise AdmissionError('exact coupled program schema')
    if 'prime_anchor'in raw and type(raw['prime_anchor'])is not bool:raise AdmissionError('prime_anchor strict optional boolean')
    if type(raw['coupled_terms'])is not list or len(raw['coupled_terms'])>MAX_TERMS:raise AdmissionError('coupled term gate128')
    base={k:raw[k]for k in ['kernel','memory','rays','drift_multiplier','gram_weights']};base.update(schema='dense-divisor-completion-v1',profiles=[],theta=[])
    p=D.parse_program(base,m);dim=p['memory']+1;terms=[];cost=16384
    for term in raw['coupled_terms']:
        if type(term)is not dict or set(term)!={'cut','weight','theta'}:raise AdmissionError('coupled term schema')
        cut=term['cut']
        if type(cut)is not dict or set(cut)!={'scale','n_exponent','u_exponent','complement','unit_balance'}:raise AdmissionError('complete cut schema')
        if type(cut['complement'])is not bool or type(cut['unit_balance'])is not bool:raise AdmissionError('strict boolean complement/unit_balance')
        scale=_rational(cut['scale'],'scale',m);ne=_rational(cut['n_exponent'],'n_exponent',m);ue=_rational(cut['u_exponent'],'u_exponent',m)
        if scale<=0:raise AdmissionError('positive cut scale')
        weight=term['weight']
        if type(weight)is not dict or weight.get('kind')not in ['one','source','product','band']or weight.get('arithmetic')not in ['all','prime','composite']:raise AdmissionError('weight kind/arithmetic')
        kind=weight['kind'];expected={'kind','arithmetic'}|({'i'}if kind=='source'else {'i','j'}if kind=='product'else {'left','right'}if kind=='band'else set())
        if set(weight)!=expected:raise AdmissionError('exact discriminated weight schema')
        parsed_weight=dict(kind=kind,arithmetic=weight['arithmetic'])
        if kind in ['source','product']:parsed_weight['i']=D.integer(weight['i'],'weight i',0,p['memory'])
        if kind=='product':
            parsed_weight['j']=D.integer(weight['j'],'weight j',parsed_weight['i'],p['memory'])
        if kind=='band':
            left=_rational(weight['left'],'band left',m);right=_rational(weight['right'],'band right',m)
            if not 0<=left<right<=1:raise AdmissionError('band0<=left<right<=1')
            parsed_weight.update(left=left,right=right)
        theta=_rational(term['theta'],'theta',m)
        if not -16<=theta<=16:raise AdmissionError('theta box[-16,16]')
        terms.append(dict(cut=dict(scale=scale,n_exponent=ne,u_exponent=ue,complement=cut['complement'],unit_balance=cut['unit_balance']),weight=parsed_weight,theta=theta))
        for v in [scale,ne,ue,theta,*[v for v in parsed_weight.values()if isinstance(v,Q)]]:cost+=512+8*(v.numerator.bit_length()+v.denominator.bit_length())
    m.reserve(cost*4);p['coupled_terms']=tuple(terms);p['prime_anchor']=raw.get('prime_anchor',False);return p

def is_prime_table(N,m):
    m.reserve(16384+8*(N+1));prime=bytearray(b'\1')*(N+1);prime[0]=0
    if N:prime[1]=0
    from math import isqrt
    for n in range(2,isqrt(N)+1):
        m.charge()
        if prime[n]:
            count=(N-n*n)//n+1;m.charge(count);prime[n*n:N+1:n]=b'\0'*count
    return prime

def weight_value(weight,n,u,N,f,prime,m):
    arithmetic=weight['arithmetic']
    if arithmetic=='prime'and not prime or arithmetic=='composite'and(n==1 or prime):return Q(0)
    kind=weight['kind']
    if kind=='one':return Q(1)
    if kind=='source':return f[weight['i']]
    if kind=='product':return _mul(f[weight['i']],f[weight['j']],m)
    left=weight['left'];right=weight['right']
    return Q(_int_mul(left.numerator,u,m)<_int_mul(n,left.denominator,m) and _int_mul(n,right.denominator,m)<=_int_mul(right.numerator,u,m))

def _vector_budget(p,N,G,m):
    common=1;largest=1
    for d,w in p['kernel']:
        common=_int_mul(common//gcd(common,w.denominator),w.denominator,m);largest=max(largest,abs(w.numerator).bit_length())
    sourcebits=2*(common.bit_length()+largest)+len(p['kernel']).bit_length()+16
    cost=16384+8*(N+1)+G*(p['memory']+1)*(512+sourcebits)
    admitted_values=[p['drift_multiplier'],*p['gram_weights'],*(w for d,w in p['kernel']),*(v for a,w in p['rays']for v in (*a,w))]
    for term in p['coupled_terms']:
        admitted_values.extend([term['theta'],term['cut']['scale'],term['cut']['n_exponent'],term['cut']['u_exponent']]);admitted_values.extend(v for v in term['weight'].values()if isinstance(v,Q))
    cost+=sum(512+8*(v.numerator.bit_length()+v.denominator.bit_length())for v in admitted_values)
    for term in p['coupled_terms']:
        kind=term['weight']['kind'];bits=2*sourcebits if kind=='product'else sourcebits if kind=='source'else 2
        if bits>100000:raise ResourceLimit('prospective source weight rational bit gate')
        cost+=G*(512+bits+max(1,N.bit_length()))
    m.reserve(cost);return cost

def _dvalue(model,k,K,n,m):
    value=Q(K//n-int(n==1))if K else Q(0);N=model['N']
    if model['program']['coupled_terms'][k]['cut']['unit_balance']and N>=2:
        correction=_mul(Q(max(K-1,0),N-1),Q(N//n-int(n==1)),m);value=_add(value,-correction,m)
    return value

def price_matrix(model,meter=None):
    """Raw complete operator, projected jointly onto optional exact prime anchor."""
    m=meter or Meter();raw=corrected_matrix(model,m)
    if not model['program']['prime_anchor']:return raw
    E=model['effective_dimension'];G=model['squarefree_count'];_budget(model,m,extra_bytes=E*E*512)
    projected=[[Q(0)for _ in range(E)]for _ in range(E)]
    for g in range(G):
        i=model['projection_indices'][g];b=model['projection_signs'][g]
        for h in range(G):
            j=model['projection_indices'][h];c=model['projection_signs'][h]
            projected[i][j]=_add(projected[i][j],_mul(Q(b*c),raw[g][h],m),m)
    return projected

def _lift_dual_weight(model,g,h,nu):
    i=model['projection_indices'][g];j=model['projection_indices'][h];sign=model['projection_signs'][g]*model['projection_signs'][h]
    if i==j:return Q(2*sign) # all known-known offdiag pairs collapse to anchor diagonal.
    if i>j:i,j=j,i
    E=model['effective_dimension'];index=i*(2*E-i-1)//2+j-i-1
    return sign*nu[index]

def _dual_functionals(model,nu,m):
    G=model['squarefree_count'];p=model['program'];dim=p['memory']+1
    # Exact common-denominator integers avoid Fraction work per template/pair.
    common=1
    vals=list(nu)+[v for row in model['features']for v in row]+[v for row in model['weights']for v in row]
    for v in vals:common=_int_mul(common//gcd(common,v.denominator),v.denominator,m)
    m.reserve(model['resident_bytes']+G*G*(512+4*common.bit_length()));m.charge(G*G*max(1,len(p['coupled_terms']))*8)
    F=[[int(v*common)for v in row]for row in model['features']]
    weights=[[int(v*common)for v in row]for row in model['weights']]
    # Offdiag lift can be odd: use denominator2common for every entry instead.
    lifted=[[2*common if g==h else int(_lift_dual_weight(model,min(g,h),max(g,h),nu)*common)for h in range(G)]for g in range(G)]
    C=[[sum(lifted[g][h]*F[g][i]*F[h][j]for g in range(G)for h in range(G))for j in range(dim)]for i in range(dim)]
    scale=2*common**3;grams=[Q(C[i][i],scale)for i in range(dim)]
    base=sum((model['T'][i][j]*Q(C[i][j],scale)for i in range(dim)for j in range(dim)),Q(0))
    zs=[];cached_key=None;rows=None
    for k,term in enumerate(p['coupled_terms']):
        if not any(weights[k]):zs.append(Q(0));continue
        key=(model['cuts'][k],term['cut']['unit_balance'])
        if key!=cached_key:rows,den=_integer_columns(model,k,m);cached_key=key
        value=sum(lifted[g][h]*rows[g][h]*weights[k][h]for g in range(G)for h in range(G))
        zs.append(Q(value,2*common*common*den))
    return base,zs,grams
