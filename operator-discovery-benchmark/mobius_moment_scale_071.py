"""Synthesize exact conditional cost programs, without arithmetic observations.

Supplied analytic rules define an affine language. A floating solver proposes
programs; exact rational primal/dual replay certifies them or leaves them open.
No optimum balance is supplied. Joined arithmetic remainders are retained.
"""
from fractions import Fraction as Q
from itertools import combinations
from math import isfinite
import warnings

from scipy.optimize import linprog, OptimizeWarning
from mobius_convolution_scale_069 import power, rational
from mobius_floor_control_068 import Meter, parameters_checked, source

PROGRAM_SCHEMA = 'mobius-moment-scale-program-v1'
SOURCE_SCHEMA = 'mobius-moment-scale-source-v1'
FLAGS = dict(conditional_prefix_bounds_paid=False, uniform_head_bound_proved=False, RH_proved=False)


def row(name, a, b):
    return dict(name=name, a=[str(Q(v)) for v in a], b=str(Q(b)))


def primary_system(sigma, rho, fixed_theta=None):
    s, r = rational(sigma), rational(rho)
    t = None if fixed_theta is None else rational(fixed_theta)
    if not 0 < s < 1 or not 0 < r < 1 or (t is not None and not 0 < t < 1):
        raise ValueError('strict fractional moment, rank and optional support split')
    rows = [row('theta_lower', [1,0,0,0,0], 0), row('theta_upper', [-1,0,0,0,0], -1),
        row('u_domain', [-1,1,0,0,0], 0), row('v_domain', [1,0,1,0,0], 1),
        row('u_rank', [0,-1,0,0,0], -r), row('v_rank', [0,0,-1,0,0], -r),
        row('u_exposure', [-1,1,0,1,0], 0), row('u_moment', [1-s,0,0,1,0], 0),
        row('v_exposure', [1,0,1,0,1], 1), row('v_moment', [s-1,0,0,0,1], s-1),
        row('u_nonpositive', [0,0,0,-1,0], 0), row('v_nonpositive', [0,0,0,0,-1], 0)]
    if t is not None:
        rows += [row('fixed_theta_lower', [1,0,0,0,0], t), row('fixed_theta_upper', [-1,0,0,0,0], -t)]
    return dict(variables=['theta','gamma_u','gamma_v','kappa_u','kappa_v'],
                rows=rows, objective=['0','0','0','1','1'])


def secondary_system(primary, optimum, rho):
    rows = [row(r['name'], r['a']+['0'], r['b']) for r in primary['rows']]
    rows += [row('optimum_lower', [0,0,0,1,1,0], optimum),
             row('optimum_upper', [0,0,0,-1,-1,0], -Q(optimum)),
             row('exposure_u', [0,-1,0,0,0,1], 0), row('exposure_v', [0,0,-1,0,0,1], 0),
             row('exposure_lower', [0,0,0,0,0,1], 0), row('exposure_upper', [0,0,0,0,0,-1], -Q(rho))]
    return dict(variables=primary['variables']+['exposure'], rows=rows, objective=['0']*5+['1'])


def short_system(sigma):
    s = rational(sigma)
    if not 0 < s < 1: raise ValueError('strict conditional short exponent')
    return dict(variables=['split','delta'], rows=[row('split_lower',[1,0],0),
        row('split_upper',[-1,0],-1), row('short_prefix',[s-1,1],s),
        row('short_tail',[1,1],1), row('delta_upper',[0,-1],-1)], objective=['0','1'])


def dot(a, b):
    return sum((x*y for x,y in zip(a,b)), Q(0))


def solve_equalities(A, b, n, meter, defaults=None):
    """Rational elimination, allowing free coordinates; no expected answer."""
    pivots = {}
    for old, rhs in zip(A,b):
        a = list(old); rhs = Q(rhs)
        for j, (p,v) in sorted(pivots.items()):
            z = a[j]
            if z:
                a = [x-z*y for x,y in zip(a,p)]; rhs -= z*v
                meter.charge(8*n+8)
        j = next((j for j,v in enumerate(a) if v), None)
        if j is None:
            if rhs: return None
            continue
        z = a[j]; pivots[j] = ([v/z for v in a], rhs/z)
        meter.charge(4*n+4)
    ans = list(defaults) if defaults is not None else [Q(0)]*n
    for j, (a,b) in sorted(pivots.items(), reverse=True):
        ans[j] = b-sum((a[k]*ans[k] for k in range(j+1,n)), Q(0))
        meter.charge(4*n+4)
    return ans


def optimal_replay(A,b,c,x,y):
    return (len(x)==len(c) and len(y)==len(b) and all(v>=0 for v in y)
        and all(dot(a,x)>=v for a,v in zip(A,b))
        and all(sum((a[k]*v for a,v in zip(A,y)),Q(0))==c[k] for k in range(len(c)))
        and dot(c,x)==dot(b,y))


def farkas_replay(A,b,y):
    return (len(y)==len(b) and all(v>=0 for v in y) and dot(b,y)==1
        and all(sum((a[k]*v for a,v in zip(A,y)),Q(0))==0 for k in range(len(A[0]))))


def _proposal(c, **kw):
    with warnings.catch_warnings():
        warnings.simplefilter('ignore', OptimizeWarning)
        return linprog(c, method='highs', options={'threads':1,'time_limit':5.0}, **kw)


def _rational_vector(v):
    if not all(isfinite(float(x)) for x in v): raise ValueError('nonfinite proposal')
    return [Q(float(x)).limit_denominator(1_000_000) for x in v]


def solve_system(system, meter=None):
    """Generic proof search. Unrepaired floating results never imply a theorem."""
    meter = Meter() if meter is None else meter
    n, m = len(system['variables']), len(system['rows'])
    if not 1<=n<=16 or not 1<=m<=128: raise ValueError('bounded affine proof language')
    A = [[rational(v) for v in r['a']] for r in system['rows']]
    b = [rational(r['b']) for r in system['rows']]; c = [rational(v) for v in system['objective']]
    if any(len(a)!=n for a in A) or len(c)!=n: raise ValueError('complete affine rows')
    meter.reserve(4*1024**2+8192*m*n); meta = {}
    try:
        res = _proposal([float(v) for v in c], A_ub=[[-float(v) for v in a] for a in A],
                        b_ub=[-float(v) for v in b], bounds=[(None,None)]*n)
        meta = dict(status=int(res.status), iterations=int(res.nit or 0), message=str(res.message))
        meter.charge(100*m*n*(1+meta['iterations']))
        if res.status == 2:
            # Search for a normalized separating combination of the rows.
            witness = _proposal([0.0]*m,
                A_eq=[[float(a[k]) for a in A] for k in range(n)]+[[float(v) for v in b]],
                b_eq=[0.0]*n+[1.0], bounds=[(0,None)]*m)
            meta['farkas_iterations'] = int(witness.nit or 0)
            meter.charge(100*m*n*(1+meta['farkas_iterations']))
            if witness.success:
                y = _rational_vector(witness.x)
                if not farkas_replay(A,b,y):
                    support = [i for i,v in enumerate(witness.x) if v>1e-10]
                    z = solve_equalities([[A[i][k] for i in support] for k in range(n)]+[[b[i] for i in support]],
                                         [Q(0)]*n+[Q(1)], len(support), meter)
                    if z is not None:
                        y=[Q(0)]*m
                        for i,v in zip(support,z): y[i]=v
                if farkas_replay(A,b,y):
                    return dict(status='infeasible', dual=list(map(str,y)), solver=meta)
            return dict(status='unresolved', reason='no exact separating certificate', solver=meta)
        if not res.success:
            return dict(status='unresolved', reason='optimizer did not propose an optimum', solver=meta)
        x, y = _rational_vector(res.x), _rational_vector(-res.ineqlin.marginals)
        candidates = [x]
        if not optimal_replay(A,b,c,x,y):
            active = [i for i,(a,v) in enumerate(zip(A,b))
                      if abs(sum(float(z)*float(t) for z,t in zip(a,res.x))-float(v)) <= 1e-7*(1+abs(float(v)))]
            repaired = solve_equalities([A[i] for i in active],[b[i] for i in active],n,meter,defaults=x)
            if repaired is not None: candidates.append(repaired)
            # Degenerate proposals may identify too many nearly active facets.
            for count,ids in enumerate(combinations(active,n)):
                if count>=2048: break
                repaired = solve_equalities([A[i] for i in ids],[b[i] for i in ids],n,meter)
                if repaired is not None: candidates.append(repaired)
            support = [i for i,v in enumerate(-res.ineqlin.marginals) if v>1e-10]
            for point in candidates:
                if not all(dot(a,point)>=v for a,v in zip(A,b)): continue
                z = solve_equalities([[A[i][k] for i in support] for k in range(n)]+[[b[i] for i in support]],
                                     c+[dot(c,point)],len(support),meter)
                if z is None: continue
                trial=[Q(0)]*m
                for i,v in zip(support,z): trial[i]=v
                if optimal_replay(A,b,c,point,trial): x,y=point,trial; break
        meter.charge(16*m*n)
        if optimal_replay(A,b,c,x,y):
            return dict(status='optimal',primal=list(map(str,x)),dual=list(map(str,y)),
                        objective=str(dot(c,x)),solver=meta)
        return dict(status='unresolved',reason='proposal failed exact primal/dual reconstruction',solver=meta)
    except (ValueError, TypeError) as exc:
        return dict(status='unresolved',reason=type(exc).__name__+': '+str(exc),solver=meta)


def construct_program(sigma, rho, fixed_theta=None, meter=None, short_cache=None):
    meter=Meter() if meter is None else meter
    primary=primary_system(sigma,rho,fixed_theta); pr=solve_system(primary,meter)
    short=short_system(sigma)
    if short_cache is not None and sigma in short_cache: sr=short_cache[sigma]
    else:
        sr=solve_system(short,meter)
        if short_cache is not None: short_cache[sigma]=sr
    second, derivation = None,None
    if pr['status']=='optimal':
        sec=secondary_system(primary,pr['objective'],rho); rr=solve_system(sec,meter)
        second=dict(system=sec,result=rr)
        if rr['status']=='optimal' and sr['status']=='optimal':
            theta,gu,gv,ku,kv,exposure=map(Q,rr['primal']); alpha=1+ku+kv
            A=(2-Q(sigma))/(1-Q(sigma)); split,delta=map(Q,sr['primal'])
            base=1/(1-exposure)
            derivation=dict(theta=str(theta),gamma_u=str(gu),gamma_v=str(gv),kappa_u=str(ku),
                kappa_v=str(kv),alpha=str(alpha),exposure=str(exposure),reciprocal_A=str(A),
                head_C_polynomial=list(map(str,[8/alpha,16*A/alpha,8*A*A/alpha])),
                short_exponent=str(delta),short_split=str(split),short_C_exponent=str(delta),
                short_per_branch_constant=str(1+4/(1-Q(sigma))),
                sufficient_base_log2=(base.numerator+base.denominator-1)//base.denominator)
    return dict(schema=PROGRAM_SCHEMA,sigma=sigma,rho=rho,fixed_theta=fixed_theta,
                primary=dict(system=primary,result=pr),secondary=second,
                short=dict(system=short,result=sr),derivation=derivation,**FLAGS)


def ceil_power(R, exponent, meter):
    a=rational(exponent); value=power(R,exponent,meter)
    meter.charge(8+R.bit_length()*max(a.numerator,a.denominator))
    return value+(value**a.denominator<R**a.numerator)


def base_gate(R, exposure, meter):
    a=1-rational(exposure)
    bits=max(R.bit_length()*a.numerator,a.denominator+1)
    if bits>100000: raise OverflowError('exact base gate power capacity')
    meter.charge(bits+8)
    return R>=3 and R**a.numerator>=2**a.denominator


def construct_source(N,y,max_j,parameters,programs,meter=None):
    meter=Meter(cap=300_000_000_000) if meter is None else meter
    if any(type(v) is not int for v in (N,y,max_j)) or not 2<=N<=65536:
        raise ValueError('bounded integer source scale')
    p,q=parameters_checked(parameters,meter); D=4*N//p
    if not 1<=y<=D or not 0<=max_j<=min(D,4096): raise ValueError('complete source row scope')
    if type(programs) is not list or not 1<=len(programs)<=128: raise ValueError('bounded proof programs')
    # Programs are proof-bearing inputs, rechecked by the independent checker.
    usable=[(i,c['derivation']) for i,c in enumerate(programs) if c['derivation'] is not None]
    endpoints=[]; cache={}
    for ratio in (Q(p,q),Q(1)):
        den=ratio.denominator; _,floors,steps=source(N,y,p,q,ratio,meter)
        rows=[]
        for j in range(1,max_j+1):
            R=D//j; joined={}
            for T,a in steps.items():
                for A,v in ((T//j,a),(T//(j+1),-a)):
                    if A: joined[A]=joined.get(A,0)+v
                meter.charge(12)
            joined={A:v for A,v in joined.items() if v}; plans=[]
            for i,d in usable:
                key=(R,d['theta'],d['gamma_u'],d['gamma_v'],d['exposure'])
                if key not in cache:
                    u=power(R,d['theta'],meter); v=power(R,str(1-Q(d['theta'])),meter)
                    tu=ceil_power(R,d['gamma_u'],meter); tv=ceil_power(R,d['gamma_v'],meter)
                    if (u+1)*(v+1)<=R or min(tu-u,tv-v)<0: raise ArithmeticError('exact support/domain gate')
                    cache[key]=(u,v,tu,tv,base_gate(R,d['exposure'],meter))
                u,v,tu,tv,gate=cache[key]
                plans.append(dict(program_index=i,u=u,v=v,T_u=tu,T_v=tv,strict_rank=max(tu,tv)<R,
                    universal_base_gate=gate,short_zero_support=(j+1)*max(u,v)<=y))
            rows.append(dict(j=j,R=R,direct_scaled=floors.get(j,0),prefix_steps=[[A,v] for A,v in sorted(joined.items())],
                b_scaled=sum(A*v for A,v in joined.items()),V_scaled=sum(map(abs,joined.values())),plans=plans))
            meter.reserve(32*1024**2+4096*(len(cache)+sum(len(r['plans']) for r in rows)))
        endpoints.append(dict(ratio=str(ratio),denominator=den,steps=[[T,a] for T,a in sorted(steps.items())],
            M1_scaled=sum(T*abs(a) for T,a in steps.items()),rows=rows))
    return dict(schema=SOURCE_SCHEMA,N=N,y=y,max_j=max_j,parameters=parameters,programs=programs,endpoints=endpoints,**FLAGS)
