"""Complete physical-coordinate divisor-cut certificate invention.

Only squarefree/prime geometry and theorems mu(1)=1, mu(p)=-1 enter search.
No unknown composite signs or observed complete source values are used. The exact Boolean diagonal
mu(n)^2=1 is retained, so row prices may be negative. Float LP proposals
are independently replaceable; certificates use exact rational matrices.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import gcd, isqrt
import time
import numpy as np
from flint import fmpq, fmpq_mat, fmpz
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
import mobius_dense_completion_082 as OLD

MAX_N=16384
MAX_COORDINATES=4096
MAX_TERMS=128
MAX_LP_NONZEROS=25_000_000
ResourceLimit=OLD.ResourceLimit
Meter=OLD.Meter


def parse_program(raw):
    keys={'schema','kernel','memory','rays','drift_multiplier','coupled_terms','gram_weights'}
    if type(raw)is not dict or not keys<=set(raw)<=keys|{'prime_anchor'} or raw['schema']!='coupled-divisor-completion-v1':
        raise ValueError('coupled program exact schema')
    if type(raw.get('prime_anchor',False))is not bool:raise ValueError('prime_anchor must be Boolean')
    base={k:deepcopy(raw[k]) for k in ('kernel','memory','rays','drift_multiplier','gram_weights')}
    base.update(schema='dense-divisor-completion-v1',profiles=[],theta=[])
    p=OLD.parse_program(base)
    p['prime_anchor']=raw.get('prime_anchor',False)
    if type(raw['coupled_terms'])is not list or len(raw['coupled_terms'])>MAX_TERMS:
        raise ValueError('coupled term budget')
    terms=[]
    for term in raw['coupled_terms']:
        if type(term)is not dict or set(term)!={'cut','weight','theta'}:
            raise ValueError('coupled term exact schema')
        cut=term['cut']
        if type(cut)is not dict or set(cut)!={'scale','n_exponent','u_exponent','complement','unit_balance'}:
            raise ValueError('cut exact schema')
        c={k:OLD.rational(cut[k]) for k in ('scale','n_exponent','u_exponent')}
        if c['scale']<=0 or type(cut['complement'])is not bool or type(cut['unit_balance'])is not bool:
            raise ValueError('cut positive scale and Boolean flags')
        c.update(complement=cut['complement'],unit_balance=cut['unit_balance'])
        w=term['weight']
        if type(w)is not dict or w.get('arithmetic')not in ('all','prime','composite'):
            raise ValueError('weight arithmetic filter')
        common={'kind','arithmetic'};kind=w.get('kind')
        if kind=='one':
            wanted=common
        elif kind in ('source','product'):
            wanted=common|({'i'} if kind=='source' else {'i','j'})
            for k in wanted-common:
                if type(w.get(k))is not int or not 0<=w[k]<=p['memory']:
                    raise ValueError('weight source index')
            if kind=='product' and w['i']>w['j']:
                raise ValueError('canonical product indices')
        elif kind=='band':
            wanted=common|{'left','right'}
            left,right=OLD.rational(w.get('left')),OLD.rational(w.get('right'))
            if not 0<=left<right<=1:
                raise ValueError('rational band domain')
        else:
            raise ValueError('weight kind')
        if set(w)!=wanted:
            raise ValueError('weight exact schema')
        theta=OLD.rational(term['theta'])
        if abs(theta)>16:
            raise ValueError('theta box')
        terms.append(dict(cut=c,weight=deepcopy(w),theta=theta))
    p['coupled_terms']=terms
    return p


def cut_value(n,u,N,cut,meter=None):
    meter=meter or Meter();a,b=cut['n_exponent'],cut['u_exponent'];scale=cut['scale']
    degree=a.denominator//gcd(a.denominator,b.denominator)*b.denominator
    ne=a.numerator*(degree//a.denominator);ue=b.numerator*(degree//b.denominator)
    bits=degree*(scale.numerator.bit_length()+scale.denominator.bit_length())+abs(ne)*n.bit_length()+abs(ue)*u.bit_length()
    if bits>OLD.MAX_BITS:
        raise ResourceLimit('coupled rational power prospective bit budget')
    numerator=scale.numerator**degree;denominator=scale.denominator**degree
    for base,exponent in ((n,ne),(u,ue)):
        if exponent>=0:numerator*=base**exponent
        else:denominator*=base**(-exponent)
    root=int(fmpz(numerator//denominator).root(degree))
    if not root**degree*denominator<=numerator<(root+1)**degree*denominator:
        raise ArithmeticError('coupled exact root check')
    meter.charge(bits+degree.bit_length())
    value=min(N,root)
    return N-value if cut['complement'] else value


def build_model(program,u,meter=None):
    meter=meter or Meter();p=parse_program(program)
    if type(u)is not int or u<1 or u.bit_length()>4096:
        raise ValueError('u positive integer domain')
    N=u//p['kernel'][0][0]
    if N>MAX_N:
        raise ResourceLimit('complete physical source horizon budget')
    T=OLD.drift_matrix(p,meter);den=1
    for _,w in p['kernel']:
        den=den//gcd(den,w.denominator)*w.denominator
        if den.bit_length()>4096:raise ResourceLimit('source denominator budget')
    integers=[(d,w.numerator*(den//w.denominator)) for d,w in p['kernel']]
    maximum=max(1,sum(abs(w)for _,w in integers))
    weight_max=max(den*den,maximum*den,maximum*maximum)
    if 4*weight_max*max(1,N)**2>=2**62:
        raise ResourceLimit('prospective physical integer basis budget')
    dim=p['memory']+1;terms=len(p['coupled_terms'])
    meter.reserve(16384+(N+1)*(96+32*(dim+terms)))
    sf=np.ones(N+1,dtype=bool);sf[0]=False
    for k in range(2,isqrt(N)+1):sf[k*k::k*k]=False;meter.charge(N//(k*k))
    prime=np.ones(N+1,dtype=bool);prime[:min(2,N+1)]=False
    for k in range(2,isqrt(N)+1):
        if prime[k]:prime[k*k::k]=False;meter.charge(N//k)
    coords=np.flatnonzero(sf);count=len(coords)
    if count>MAX_COORDINATES:
        raise ResourceLimit('complete physical matrix coordinate budget; no truncation')
    F=np.zeros((count,dim),dtype=np.int64)
    known=(coords==1)|prime[coords]
    known_signs=np.where(coords==1,1,np.where(prime[coords],-1,0)).astype(np.int64)
    composite_indices=np.flatnonzero(~known)
    price_dimension=(1+len(composite_indices)if count else 0)if p['prime_anchor']else count
    for i in range(dim):
        for d,w in integers:F[:,i]+=(coords<=u//((1<<i)*d))*w
    cuts=[];weights=[];cache={}
    for term in p['coupled_terms']:
        c=term['cut'];key=tuple(c[k] for k in ('scale','n_exponent','u_exponent','complement'))
        if key not in cache:cache[key]=np.array([cut_value(int(n),u,N,c,meter) for n in coords],dtype=np.int64)
        cuts.append(cache[key]);w=term['weight'];kind=w['kind']
        if kind=='one':values=np.full(count,den*den,dtype=np.int64)
        elif kind=='source':values=F[:,w['i']]*den
        elif kind=='product':values=F[:,w['i']]*F[:,w['j']]
        else:
            l,r=Q(w['left']),Q(w['right'])
            # Comparisons remain exact even for large rational band denominators.
            values=np.array([den*den*int(l.numerator*u<int(n)*l.denominator and int(n)*r.denominator<=r.numerator*u) for n in coords],dtype=np.int64)
        if w['arithmetic']=='prime':values=values*prime[coords]
        elif w['arithmetic']=='composite':values=values*((coords>1)&~prime[coords])
        weights.append(values)
    meter.charge((N+1)*max(1,dim+terms))
    resident=16384+64*(N+1)+count*(128+16*(dim+2*terms))+32768*(len(p['rays'])+len(p['kernel'])+terms)
    meter.reserve(resident)
    return dict(raw=deepcopy(program),program=p,u=u,N=N,coordinates=coords,
                squarefree_count=count,prime_count=int(prime.sum()),features=F,
                denominator=den,T=T,cuts=cuts,weights=weights,meter=meter,_cached_D=None,
                resident_bytes=resident,extra_resident_bytes=0,known_signs=known_signs,
                composite_indices=composite_indices,price_dimension=price_dimension)


def _basis_budget(model,extra=0):
    count=model['squarefree_count'];p=model['program']
    vals=[q for row in model['T']for q in row]+[t['theta']for t in p['coupled_terms']]+list(p['gram_weights'])
    bits=OLD.rational_budget(vals,model['meter'],terms=max(1,len(vals)))
    bits+=4*model['denominator'].bit_length()+4*max(1,model['N'].bit_length())+64
    if bits>OLD.MAX_BITS:raise ResourceLimit('prospective native matrix rational budget')
    model['meter'].reserve(model['resident_bytes']+model.get('extra_resident_bytes',0)+count*count*(1152+3*bits)+extra)


def coupled_basis(model,index):
    """Return integer symmetric numerator and common rational denominator."""
    count=model['squarefree_count']
    model['meter'].reserve(model['resident_bytes']+model.get('extra_resident_bytes',0)+count*count*96)
    n=model['coordinates'];K=model['cuts'][index];term=model['program']['coupled_terms'][index]
    balance=term['cut']['unit_balance'] and model['N']>=2
    key=(id(K),balance)
    cached=model['_cached_D']
    if cached is None or cached[0]!=key:
        D=K[None,:]//n[:,None]-(n[:,None]==1)*(K[None,:]>0)
        divisor=1
        if balance:
            divisor=model['N']-1
            Cfull=model['N']//n-(n==1)
            D=divisor*D-Cfull[:,None]*np.maximum(K-1,0)[None,:]
        model['_cached_D']=(key,D,divisor)
    else:_,D,divisor=cached
    weighted=D*model['weights'][index][None,:]
    return weighted+weighted.T,2*model['denominator']**2*divisor


def project_float(model,A):
    if not model['program']['prime_anchor']or not model['squarefree_count']:return A
    b=model['known_signs'].astype(float);indices=model['composite_indices'];q=A@b
    result=np.empty((len(indices)+1,len(indices)+1));result[0,0]=b@q
    result[0,1:]=q[indices];result[1:,0]=q[indices];result[1:,1:]=A[np.ix_(indices,indices)]
    return result


def project_native(model,A):
    if not model['program']['prime_anchor']or not model['squarefree_count']:return A
    b=fmpq_mat([[int(v)]for v in model['known_signs']]);q=A*b
    indices=list(map(int,model['composite_indices']));n=len(indices)+1
    result=fmpq_mat(n,n);result[0,0]=(b.transpose()*q)[0,0]
    for i,raw_i in enumerate(indices,1):
        result[0,i]=result[i,0]=q[raw_i,0]
        for j,raw_j in enumerate(indices,1):result[i,j]=A[raw_i,raw_j]
    return result


def native_matrix(model,raw=False):
    _basis_budget(model);p=model['program'];F=model['features'];n=len(F);den=model['denominator']
    if not n:return fmpq_mat(0,0)
    T=[[model['T'][i][j]+(p['gram_weights'][i]if i==j else 0)
        for j in range(p['memory']+1)]for i in range(p['memory']+1)]
    nativeF=fmpq_mat(F.tolist());nativeT=fmpq_mat([[str(q)for q in row]for row in T])
    A=nativeF*nativeT*nativeF.transpose()/fmpq(den*den)
    model['meter'].charge(n*n*(p['memory']+1))
    for i,term in enumerate(p['coupled_terms']):
        if not term['theta']:continue
        numerator,denominator=coupled_basis(model,i);factor=term['theta']/denominator
        A+=fmpq_mat(numerator.tolist())*fmpq(factor.numerator,factor.denominator)
        model['meter'].charge(n*n*8)
    return A if raw else project_native(model,A)


def upper_certificate(model):
    original=native_matrix(model,raw=True);A=project_native(model,original);n=model['price_dimension'];rows=[]
    unit_cost=Q(0);diagonal=Q(0)
    for i in range(n):
        value=A[i,i];diagonal+=OLD.as_q(value)
        for j in range(n):
            if i!=j:value+=abs(A[i,j])
        rows.append(OLD.as_q(value))
    for i in range(1,model['squarefree_count']):unit_cost+=2*abs(OLD.as_q(original[0,i]))
    certificate=dict(squarefree_count=model['squarefree_count'],price=str(sum(rows,Q(0))),row_prices=list(map(str,rows)))
    return certificate,dict(trace=str(diagonal),unit_offdiagonal_absolute_price=str(unit_cost),
                            negative_row_prices=sum(q<0 for q in rows),prime_count=model['prime_count'],
                            price_dimension=n,all_actual_prime_signs_anchored=model['program']['prime_anchor'])


def dual_certificate(model,nus):
    n=model['squarefree_count'];effective=model['price_dimension'];edges=n*(n-1)//2
    if type(nus)is not list or len(nus)!=effective*(effective-1)//2:raise ValueError('dual pair dimension')
    admitted=[]
    for value in nus:
        q=OLD.rational(value) if type(value)is str else value
        if type(q)is int:q=Q(q)
        if type(q)is not Q or max(q.numerator.bit_length(),q.denominator.bit_length())>4096 or abs(q)>2:
            raise ValueError('exact feasible dual pair required')
        admitted.append(q)
    supplied=admitted
    if model['program']['prime_anchor']:
        positions={int(i):k+1 for k,i in enumerate(model['composite_indices'])}
        b=model['known_signs'];admitted=[]
        model['meter'].reserve(model['resident_bytes']+model.get('extra_resident_bytes',0)+edges*128)
        for i in range(n):
            for j in range(i+1,n):
                if b[i] and b[j]:q=Q(2*int(b[i])*int(b[j]))
                elif b[i]:q=int(b[i])*supplied[positions[j]-1]
                elif b[j]:q=int(b[j])*supplied[positions[i]-1]
                else:
                    a,c=positions[i],positions[j]
                    q=supplied[a*(2*effective-a-1)//2+c-a-1]
                admitted.append(q)
    _basis_budget(model)
    bits=OLD.rational_budget(admitted,model['meter'],terms=max(1,edges))
    model['meter'].reserve(model['resident_bytes']+model.get('extra_resident_bytes',0)+
                           n*n*(768+3*bits)+edges*(512+bits))
    if not n:return dict(nu=[],lower_bound='0')
    g,h=np.triu_indices(n,1)
    D=fmpq_mat(n,n)
    for i in range(n):D[i,i]=1
    for k,(i,j) in enumerate(zip(g,h)):
        q=admitted[k]/2;D[int(i),int(j)]=D[int(j),int(i)]=fmpq(q.numerator,q.denominator)
    F=fmpq_mat(model['features'].tolist());small=F.transpose()*D*F/fmpq(model['denominator']**2)
    dim=model['program']['memory']+1
    lower=sum((model['T'][i][j]*OLD.as_q(small[i,j])for i in range(dim)for j in range(dim)),Q(0))
    lower+=16*sum((min(Q(0),OLD.as_q(small[i,i]))for i in range(dim)),Q(0))
    for j in range(len(model['cuts'])):
        numerator,den=coupled_basis(model,j)
        value=sum((Q(int(numerator[i,i]),den)for i in range(n)),Q(0))
        # Native vector dot performs denominator accumulation exactly, bounded above.
        if edges:
            left=fmpq_mat([[int(x)for x in numerator[g,h]]])
            right=fmpq_mat([[str(q)]for q in admitted])
            value+=OLD.as_q((left*right)[0,0])/den
        lower-=16*abs(value)
        model['meter'].charge(n*n*4)
    return dict(nu=list(map(str,supplied)),lower_bound=str(lower))


def parameter_basis(model):
    _basis_budget(model)
    F=model['features'].astype(float)/model['denominator']
    if model['program']['prime_anchor']and model['squarefree_count']:
        F=np.vstack((model['known_signs']@F,F[model['composite_indices'],:]))
    n,dim=F.shape
    T=np.array([[float(q)for q in row]for row in model['T']]);A0=F@T@F.T
    g,h=np.triu_indices(n,1);count=len(model['cuts'])+dim
    diag=np.empty((n,count));off=np.empty((len(g),count))
    for j in range(len(model['cuts'])):
        numerator,den=coupled_basis(model,j);value=project_float(model,numerator.astype(float))/den
        diag[:,j]=np.diag(value);off[:,j]=value[g,h]
    for i in range(dim):
        j=len(model['cuts'])+i;diag[:,j]=F[:,i]**2;off[:,j]=F[g,i]*F[h,i]
    return A0,diag,off,g,h


def reconstruct_parameters(floats,equalities,bounds,meter):
    """Project rounded free variables onto an exact affine proof family."""
    size=len(bounds)
    if equalities is None:
        return [max(Q(lo),min(Q(hi),OLD.rounded(x)))for x,(lo,hi)in zip(floats,bounds)],[]
    if type(equalities)is not dict or set(equalities)!={'rows','rhs'} or len(equalities['rows'])!=len(equalities['rhs']) or len(equalities['rows'])>2*size+2:
        raise ValueError('bounded equality system shape')
    rows=[]
    for row,rhs in zip(equalities['rows'],equalities['rhs']):
        if len(row)!=size:raise ValueError('equality coefficient count')
        rows.append([OLD.rational(q)for q in row]+[OLD.rational(rhs)])
    bits=OLD.rational_budget([q for row in rows for q in row],meter,terms=max(1,len(rows)*size))
    if bits*(size+1)>OLD.MAX_BITS:raise ResourceLimit('exact affine reconstruction determinant budget')
    meter.reserve(16384+(size+1)**2*(256+bits*(size+1)))
    attempts=[]
    for active_tolerance in (1e-8,0.0):
        augmented=deepcopy(rows)
        for i,(x,(lo,hi))in enumerate(zip(floats,bounds)):
            target=lo if abs(x-lo)<=active_tolerance else hi if abs(x-hi)<=active_tolerance else None
            if target is not None:
                row=[Q(int(j==i))for j in range(size)]+[Q(target)];augmented.append(row)
        if not augmented:
            return [OLD.rounded(x)for x in floats],attempts
        R,rank=fmpq_mat([[str(q)for q in row]for row in augmented]).rref()
        pivots=[];inconsistent=False
        for i in range(rank):
            pivot=next((j for j in range(size+1)if R[i,j]),None)
            if pivot==size:inconsistent=True;break
            if pivot is not None:pivots.append((i,pivot))
        meter.charge((size+1)**3)
        if inconsistent:
            attempts.append(dict(active_tolerance=active_tolerance,status='INCONSISTENT_ACTIVE_FACE'));continue
        pivot_set={j for _,j in pivots}
        for precision in (24,32,40,48):
            values=[max(Q(lo),min(Q(hi),OLD.rounded(x,precision)))for x,(lo,hi)in zip(floats,bounds)]
            for i,pivot in pivots:
                values[pivot]=OLD.as_q(R[i,size])-sum((OLD.as_q(R[i,j])*values[j]for j in range(size)if j not in pivot_set),Q(0))
            valid=all(Q(lo)<=v<=Q(hi)for v,(lo,hi)in zip(values,bounds))
            valid=valid and all(sum((r[j]*values[j]for j in range(size)),Q(0))==r[-1]for r in rows)
            attempts.append(dict(active_tolerance=active_tolerance,bits=precision,status='EXACT'if valid else'OUTSIDE_BOX'))
            if valid:return values,attempts
    return None,attempts


def optimize(program,u,time_limit=180,equalities=None):
    started=time.monotonic();model=build_model(program,u);n=model['price_dimension']
    theta_count=len(model['cuts']);dim=model['program']['memory']+1;count=theta_count+dim;edges=n*(n-1)//2
    prospective=2*edges*(count+1)
    if prospective>MAX_LP_NONZEROS:raise ResourceLimit('complete LP nonzero budget')
    model['meter'].reserve(model['resident_bytes']+prospective*96+edges*count*24+n*n*256)
    A0,diag,off,g,h=parameter_basis(model);scale=float(u*u)
    diag/=scale;off/=scale;A0/=scale
    ar,ac=np.nonzero(off);ee=np.arange(edges)
    rows=np.concatenate((2*ar,2*ar+1,2*ee,2*ee+1))
    columns=np.concatenate((ac,ac,count+ee,count+ee))
    values=np.concatenate((off[ar,ac],-off[ar,ac],-np.ones(edges),-np.ones(edges)))
    matrix=coo_matrix((values,(rows,columns)),shape=(2*edges,count+edges)).tocsr()
    rhs=np.empty(2*edges);rhs[::2]=-A0[g,h];rhs[1::2]=A0[g,h]
    objective=np.concatenate((diag.sum(axis=0),2*np.ones(edges)))
    parameter_bounds=[(-16,16)]*theta_count+[(0,16)]*dim
    eq_matrix=eq_rhs=None
    if equalities is not None:
        # Admit dimensions/canonical exact coefficients before float proposal conversion.
        reconstruct_parameters([0.0]*count,equalities,parameter_bounds,model['meter'])
        eq_matrix=np.zeros((len(equalities['rows']),count+edges))
        eq_matrix[:,:count]=np.array([[float(Q(q))for q in row]for row in equalities['rows']])
        eq_rhs=np.array([float(Q(q))for q in equalities['rhs']])
    fit=linprog(objective,A_ub=matrix,b_ub=rhs,A_eq=eq_matrix,b_eq=eq_rhs,
                bounds=parameter_bounds+[(0,None)]*edges,
                method='highs',options={'time_limit':time_limit,'dual_feasibility_tolerance':1e-8,'primal_feasibility_tolerance':1e-8})
    report=dict(status='LP_PROPOSAL'if fit.success else'LP_NO_PROPOSAL',solver_status=int(fit.status),
                solver_message=str(fit.message),u=u,squarefree_count=model['squarefree_count'],price_dimension=n,
                prime_signs_anchored=model['program']['prime_anchor'],prime_count=model['prime_count'],nonzeros=int(matrix.nnz),
                elapsed_seconds=time.monotonic()-started,ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes,
                unknown_composite_signs_used=False,observed_full_source_values_used=False,
                known_prime_signs_anchored=model['program']['prime_anchor'],
                uniform_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
    if not fit.success:return report
    float_optimum=float(fit.fun+np.trace(A0))
    # Large LP arrays are no longer needed during exact matrix admissions.
    del matrix,rhs,objective,rows,columns,values,ar,ac,ee,diag,off,A0,eq_matrix,eq_rhs,g,h
    model['extra_resident_bytes']=128*(count+edges)+16*edges
    exact,reconstruction=reconstruct_parameters(list(fit.x[:count]),equalities,parameter_bounds,model['meter'])
    report['equality_reconstruction']=reconstruction
    report['proof_equalities']=equalities
    if exact is None:
        report.update(status='LP_EXACT_EQ_RECONSTRUCTION_FAILED',float_parameters=list(map(float,fit.x[:count])))
        return report
    proposal=deepcopy(program)
    for i,term in enumerate(proposal['coupled_terms']):
        term['theta']=str(exact[i])
    proposal['gram_weights']=list(map(str,exact[theta_count:count]))
    fitted=dict(model,raw=proposal,program=parse_program(proposal))
    certificate,diagnostics=upper_certificate(fitted)
    marg=fit.ineqlin.marginals
    nus=[max(Q(-2),min(Q(2),OLD.rounded(-marg[2*i]+marg[2*i+1])))for i in range(edges)]
    dual=dual_certificate(model,nus)
    gap=Q(certificate['price'])-Q(dual['lower_bound'])
    if gap<0:raise ArithmeticError('exact Boolean primal/dual ordering')
    report.update(program=proposal,certificate=certificate,diagnostics=diagnostics,dual=dual,exact_gap=str(gap),
                  dual_scope='finite lower price for all parameter boxes, without using optional affine proof constraints',
                  float_optimum_over_u2=float_optimum,
                  elapsed_seconds=time.monotonic()-started,ops=model['meter'].ops,prospective_peak_bytes=model['meter'].peak_bytes)
    return report
