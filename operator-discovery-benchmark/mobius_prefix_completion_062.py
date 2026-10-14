"""Discover exact finite prefix controls by complete-floor reconstruction.

Only floor geometry and the registered coprimality mask enter optimization.
The ordinary small-index Mobius function builds a generic inverse dictionary;
actual source Mobius signs and measured prefix values never enter the LP.
Floating optimization proposes coefficients. Exact replay admits a bound.
"""
from fractions import Fraction as Q
from math import gcd, isqrt, prod
import time

from prime_transfer_algebra_058 import Meter

MAX_N=65536
MAX_HORIZONS=4096


def weight(N,b,d):
    return (4*N)//(b*d)-3*((2*N)//(b*d))+2*(N//(b*d))


def ordinary_mu(n,meter):
    """Small inverse-kernel coefficients, not a source-arithmetic sieve."""
    mu=[1]*(n+1);prime=[True]*(n+1);mu[0]=0
    for p in range(2,n+1):
        meter.charge()
        if not prime[p]:continue
        for j in range(p,n+1,p):
            prime[j]=False;mu[j]*=-1;meter.charge(3)
        for j in range(p*p,n+1,p*p):mu[j]=0;meter.charge()
    return mu


def indicators(Z,y,H,meter):
    """floor(Z/d)*1[d<=y] as aggregated indicators with endpoint>H."""
    out={};m=1;last=Z//(H+1)
    while m<=last:
        v=Z//m;end=min(last,Z//v);T=min(y,v)
        if T>H:out[T]=out.get(T,0)+end-m+1
        m=end+1;meter.charge(12)
    return out


def inverse_completion(N,y,H,parameters,meter=None):
    meter=Meter() if meter is None else meter
    p,q=parameters['p'],parameters['q'];D=4*N//p
    if type(N) is not int or not 2<=N<=MAX_N or not 1<=H<=D or not 1<=y<=D:
        raise ValueError('finite source/cutoff range')
    cap=min(y,D)//(H+1);mu=ordinary_mu(cap,meter);columns=[]
    for b in (p,q):
        changes={}
        for factor,c in ((4,1),(2,-3),(1,2)):
            for T,a in indicators(factor*N//b,y,H,meter).items():
                changes[T]=changes.get(T,0)+c*a;meter.charge(3)
        column={}
        for T,a in changes.items():
            if not a:continue
            for ell in range(1,T//(H+1)+1):
                meter.charge(8)
                if mu[ell]:
                    X=T//ell;column[X]=column.get(X,0)+a*mu[ell]
        columns.append({X:Q(c) for X,c in column.items() if c})
    endpoints=[]
    for r in (Q(p,q),Q(1)):
        keys=set(columns[0])|set(columns[1])
        endpoints.append({X:columns[0].get(X,Q(0))-r*columns[1].get(X,Q(0)) for X in keys})
    return {'columns':columns,'endpoints':endpoints,'ordinary_inverse_index_max':cap}


def exact_certificate(N,y,H,parameters,endpoints,meter=None):
    meter=Meter() if meter is None else meter
    horizons=sorted(X for X in set(endpoints[0])|set(endpoints[1])
                    if endpoints[0].get(X,0) or endpoints[1].get(X,0))
    if len(horizons)>MAX_HORIZONS or any(type(X) is not int or not 1<=X<=4*N for X in horizons):
        raise OverflowError('complete floor dictionary capacity')
    coefficients=[[Q(row.get(X,0)) for X in horizons] for row in endpoints]
    costs=[sum(map(abs,row),Q(0)) for row in coefficients]
    p,q=parameters['p'],parameters['q'];R=prod(parameters['primes']);D=4*N//p
    for d in range(1,max([D]+horizons)+1):
        meter.charge(8)
        if gcd(d,R)!=1:continue
        A=weight(N,p,d) if d<=y else 0;B=weight(N,q,d) if d<=y else 0
        floors=[X//d for X in horizons]
        for e,r in enumerate((Q(p,q),Q(1))):
            completed=sum((c*f for c,f in zip(coefficients[e],floors) if f),Q(0))
            residual=A-r*B-completed;meter.charge(12*len(horizons)+16)
            if d>H and residual:raise ValueError('proposed rational coefficients fail exact tail replay')
            if d<=H:costs[e]+=abs(residual)
    return {'schema':'mobius-prefix-completion-v1','parameters':parameters,
            'N':N,'y':y,'H':H,'horizons':horizons,'ratios':[str(Q(p,q)),'1'],
            'coefficients':[[str(c) for c in row] for row in coefficients],
            'budget':str(max(costs))}


def dictionary(N,y,H,parameters,base,meter=None):
    """Reciprocal closure plus moving, small and extended horizons."""
    meter=Meter() if meter is None else meter
    horizons=set(range(1,H+1))
    for row in base['endpoints']:horizons.update(row)
    seeds={factor*N//b for factor in (1,2,4) for b in (parameters['p'],parameters['q'])}
    seeds.update(min(4*N,multiplier*y) for multiplier in (1,2,3,4))
    for Z in seeds:
        ell=1
        while ell<=Z//(H+1):
            v=Z//ell;horizons.add(v);ell=Z//v+1;meter.charge(12)
    horizons=sorted(horizons)
    if len(horizons)>MAX_HORIZONS:raise OverflowError('LP floor dictionary capacity')
    return horizons


def constraint_rows(N,y,H,parameters,horizons,meter):
    """Compress equal tail rows; retain a separate residual for each short d."""
    R=prod(parameters['primes']);p,q=parameters['p'],parameters['q']
    end=max([4*N//p]+horizons);m=len(horizons)
    meter.reserve(64*1024**2+48*(end+1)*(m+1))
    rows=[];targets=[];short=[];seen=set();coprime_tail=0
    for d in range(1,end+1):
        meter.charge(10)
        if gcd(d,R)!=1:continue
        row=tuple(X//d for X in horizons)
        target=(weight(N,p,d),weight(N,q,d)) if d<=y else (0,0)
        meter.charge(m*4+20)
        if d<=H:
            short.append(len(rows));rows.append(row);targets.append(target)
        else:
            coprime_tail+=1;key=(row,target)
            if key not in seen:
                seen.add(key);rows.append(row);targets.append(target)
    return rows,targets,short,{'tail_checked_through':end,'coprime_tail_rows':coprime_tail,
        'lp_equality_rows':len(rows),'short_residual_variables':len(short)}


def lp_completion(N,y,H,parameters,horizons,meter=None,balanced=False,
                  max_denominator=1_000_000,time_limit=120):
    """Minimize complete endpoint L1 budgets; exact replays decide admission."""
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csc_matrix,hstack,vstack
    meter=Meter() if meter is None else meter
    started=time.monotonic();rows,targets,short,shape=constraint_rows(N,y,H,parameters,horizons,meter)
    m=len(horizons);nr=len(rows);ns=len(short)
    floors=csc_matrix(np.asarray(rows,dtype=np.float64))
    residual=csc_matrix((np.ones(ns),(short,range(ns))),shape=(nr,ns))
    A=hstack((floors,residual),format='csc')
    if balanced:A=vstack((A,csc_matrix([horizons+[0]*ns])),format='csc')
    signed=hstack((A,-A),format='csc');objective=np.ones(2*(m+ns))
    endpoints=[];attempts=[]
    p,q=parameters['p'],parameters['q']
    for r in (Q(p,q),Q(1)):
        b=np.asarray([float(Q(a)-r*c) for a,c in targets]+([0.0] if balanced else []))
        result=linprog(objective,A_eq=signed,b_eq=b,bounds=(0,None),method='highs-ds',
                       options={'time_limit':time_limit,'primal_feasibility_tolerance':1e-9,
                                'dual_feasibility_tolerance':1e-9})
        meter.charge(signed.nnz*4+max(0,int(result.nit or 0))*(signed.shape[0]+signed.shape[1]))
        attempt={'ratio':str(r),'success':bool(result.success),'status':int(result.status),
                 'message':result.message,'iterations':int(result.nit or 0),
                 'objective_float':float(result.fun) if result.fun is not None else None}
        attempts.append(attempt)
        if not result.success:
            return {'admitted':False,'reason':'LP did not supply a candidate','attempts':attempts,
                    'shape':shape,'balanced':balanced,'elapsed_seconds':time.monotonic()-started}
        xs=result.x[:m]-result.x[m+ns:m+ns+m]
        row={X:Q(float(x)).limit_denominator(max_denominator) for X,x in zip(horizons,xs) if abs(x)>1e-10}
        if balanced and sum((X*c for X,c in row.items()),Q(0)):
            return {'admitted':False,'reason':'exact first moment failed after rationalization',
                    'attempts':attempts,'shape':shape,'balanced':balanced,
                    'proposed_coefficients':{str(X):str(c) for X,c in row.items()},
                    'elapsed_seconds':time.monotonic()-started}
        endpoints.append(row)
    try:cert=exact_certificate(N,y,H,parameters,endpoints,meter)
    except (ValueError,OverflowError) as exc:
        return {'admitted':False,'reason':str(exc),'attempts':attempts,'shape':shape,'balanced':balanced,
                'proposed_coefficients':[{str(X):str(c) for X,c in row.items()} for row in endpoints],
                'elapsed_seconds':time.monotonic()-started}
    return {'admitted':True,'certificate':cert,'attempts':attempts,'shape':shape,
            'balanced':balanced,'objective_optimality_proved':False,
            'elapsed_seconds':time.monotonic()-started}


def search_one(N,y,H,parameters,meter=None):
    meter=Meter() if meter is None else meter
    base=inverse_completion(N,y,H,parameters,meter)
    cert=exact_certificate(N,y,H,parameters,base['endpoints'],meter)
    horizons=dictionary(N,y,H,parameters,base,meter)
    candidates=[{'kind':'generic_indicator_inverse','admitted':True,'certificate':cert,
                 'ordinary_inverse_index_max':base['ordinary_inverse_index_max']}]
    for balanced in (False,True):
        candidate=lp_completion(N,y,H,parameters,horizons,meter,balanced)
        candidate['kind']='joint_lp_zero_moment' if balanced else 'joint_lp';candidates.append(candidate)
    selected=min((c for c in candidates if c['admitted']),key=lambda c:(Q(c['certificate']['budget']),len(c['certificate']['horizons']),c['kind']))
    return {'N':N,'y':y,'H':H,'dictionary_size':len(horizons),'dictionary_max':max(horizons),
            'candidates':candidates,'selected_kind':selected['kind'],
            'selected_budget':selected['certificate']['budget'],
            'source_mu_signs_or_prefix_values_used':False,'uniform_growth_proved':False}
