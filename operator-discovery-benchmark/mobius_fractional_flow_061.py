"""Infer positive parameterized masses and a joint-prefix bound construction.

Source kernel atoms and a previously proved periodic signature are inputs.
Selection uses exact bound exponents, before any arithmetic prefix values.
Numerical integration is descriptive only; it never proves core growth.
"""
from fractions import Fraction as Q
from math import exp,expm1,fsum,isfinite,lgamma,log,log1p,prod

from prime_transfer_algebra_058 import Meter
from mobius_transport_search_059 import _q,_tokens,exponent_grid,floor_power
from mobius_mass_conservation_060 import PROFILES,identity

MAX_TOKENS=400_000
MAX_BREAKPOINTS=8192
MAX_GRID=4096
NODE_BATCH=128


def infer_masses(parameters,kernels,compiled,meter=None):
    meter=meter or Meter()
    if type(kernels) is not dict or set(kernels)!=set(PROFILES):raise ValueError('complete profile kernels')
    values={};prefixes={}
    for name in PROFILES:
        rows=kernels[name]
        if type(rows) is not list or not 1<=len(rows)<=16:raise ValueError('bounded nonempty kernel polynomial')
        coeffs={};last=0;total=Q(0);prefix=[]
        for row in rows:
            if type(row) is not list or len(row)!=2:raise ValueError('base and rational coefficient')
            base,c=row[0],_q(row[1])
            if type(base) is not int or not last<base<=1_000_000 or not c:raise ValueError('canonical kernel atoms')
            coeffs[base]=c;last=base;total+=c;prefix.append(str(total));meter.charge(16)
        if any(Q(v)<0 for v in prefix) or not any(Q(v)>0 for v in prefix):
            raise ValueError('positive exponential kernel requires a proved prefix cone')
        values[name]=coeffs;prefixes[name]=prefix
    columns=[]
    for base in sorted({b for row in values.values() for b in row}):
        vector=[str(values[name].get(base,Q(0))) for name in PROFILES]
        found=identity(parameters,vector,compiled,meter)
        if found is None:raise ValueError('a kernel column has no complete mass conservation')
        columns.append({'base':base,'identity':found})
    H=sum(abs(Q(row['c'])) for column in columns for row in column['identity']['floor_coefficients'])
    k=len(parameters['primes']);R=prod(parameters['primes']);alpha=_q(parameters['alpha'])
    return {'kernels':kernels,'columns':columns,'positive_prefixes':prefixes,
            'endpoint_coefficient':str(Q(3*R)*H/(k-alpha)),
            'head_coefficient':str(Q(6*R)/(k+1-alpha)),
            'exit_coefficient':str(Q(6*parameters['p']*R)/(k+1-alpha)),
            'log_degree':k,'carrier':'d^(-t)','horizon':'max(1,floor(4*N/p))'}


def discover(parameters,kernels,compiled,max_denominator=12,meter=None):
    meter=meter or Meter();inferred=infer_masses(parameters,kernels,compiled,meter)
    grid=sorted({Q(0)}|set(exponent_grid(max_denominator)))
    if len(grid)**2>MAX_GRID:raise OverflowError('prospective cutoff grammar capacity')
    rows=[];admitted=[]
    for theta in grid:
        for rho in grid:
            head,exit=theta,2*rho-1;valid=head<=Q(1,2) and exit<=Q(1,2)
            row={'head_theta':str(theta),'exit_rho':str(rho),'head_power':str(head),
                 'exit_power':str(exit),'admissible_square_root_components':valid}
            rows.append(row);meter.charge(24)
            if valid:admitted.append(row)
    # Increasing either cutoff shrinks the remaining core pointwise. Its
    # largest admissible pair is selected by this exact interval inclusion.
    admitted.sort(key=lambda r:(-Q(r['head_theta']),-Q(r['exit_rho'])))
    selected=admitted[0]
    cert={'schema':'mobius-fractional-flow-v1','parameters':parameters,**inferred,
          'head_theta':selected['head_theta'],'exit_rho':selected['exit_rho']}
    return {'schema':'mobius-fractional-flow-discovery-v1','parameters':parameters,
            'kernel_columns_inferred':len(inferred['columns']),'cutoff_grid':[str(x) for x in grid],
            'cutoff_rows':rows,'admitted_cutoff_pairs':len(admitted),'selected':cert,
            'selection':'largest head and exit cutoffs with independently affordable powers; remaining-core interval inclusion',
            'source_values_used':False,'uniform_core_bound_proved':False}


def prefix_table(tokens,kernels,meter=None):
    meter=meter or Meter();by_d=_tokens(tokens)
    if len(tokens)>MAX_TOKENS:raise MemoryError('prefix table capacity')
    bases=sorted({b for terms in kernels.values() for b,c in terms})
    if len(bases)!=2:raise ValueError('two-atom root partition required by this numerical evaluator')
    coeffs={name:[sum((_q(c) for b,c in terms if b==base),Q(0)) for base in bases]
            for name,terms in kernels.items()}
    if any(c.denominator!=1 or abs(c.numerator)>16 for row in coeffs.values() for c in row):
        raise ValueError('bounded integer source atom columns for prefix evaluator')
    cumulative=[0,0];rows=[]
    for d in sorted(by_d):
        token=by_d[d]
        cumulative=[s+token['sign']*int(c) for s,c in zip(cumulative,coeffs[token['profile']])]
        rows.append({'d':d,'coefficients':list(cumulative)});meter.charge(32)
    meter.reserve(1024+len(rows)*1024)
    return {'bases':bases,'rows':rows,'total_coefficients':list(cumulative),
            'ordinary_signs_included':True,'numerical_values_used':False}


def root_ratios(table,meter=None):
    """Each two-exponential prefix has at most one positive-t zero."""
    meter=meter or Meter();ratios=set()
    for row in table['rows']:
        u,v=row['coefficients'];meter.charge(16)
        if u*v<0:
            ratio=Q(-u,v)
            if 0<ratio<1:ratios.add(ratio)
    if len(ratios)>MAX_BREAKPOINTS:raise OverflowError('prospective prefix-root capacity')
    return sorted(ratios)


def rational_transport(positions,signed_masses,carriers,meter=None):
    """Exact synthetic primal/dual calibration for partial fractional flows."""
    meter=meter or Meter()
    if not len(positions)==len(signed_masses)==len(carriers):raise ValueError('complete discrete transport')
    masses=[Q(v) for v in signed_masses];xs=[Q(v) for v in carriers]
    if positions!=sorted(set(positions)) or any(x<=0 for x in xs) or any(a<=b for a,b in zip(xs,xs[1:])):
        raise ValueError('strict cofactor/carrier order')
    stack=[];pairs=[];pair_cost=Q(0);prefix=Q(0);dual=Q(0)
    for i,mass in enumerate(masses):
        prefix+=mass;dual+=abs(prefix)*(xs[i]-(xs[i+1] if i+1<len(xs) else 0))
        sign=1 if mass>0 else -1;remaining=abs(mass)
        while remaining and stack and stack[-1][2]!=sign:
            j,available,other_sign=stack.pop();amount=min(available,remaining)
            pairs.append({'i':j,'j':i,'mass':str(amount)})
            pair_cost+=amount*abs(xs[j]-xs[i]);remaining-=amount;available-=amount
            if available:stack.append((j,available,other_sign))
            meter.charge(24)
        if remaining:stack.append((i,remaining,sign))
        meter.charge(16)
    leftover= sum((amount*xs[j] for j,amount,sign in stack),Q(0))
    if pair_cost+leftover!=dual:raise ArithmeticError('exact fractional primal/prefix equality')
    return {'pairs':pairs,'leftover_mass':str(sum((r[1] for r in stack),Q(0))),
            'pair_cost':str(pair_cost),'leftover_cost':str(leftover),'prefix_cost':str(dual),
            'terminal_term':str(abs(prefix)*xs[-1] if xs else Q(0))}


def evaluate_saved_tokens(N,parameters,kernels,tokens,head_theta,exit_rho,degree=16,meter=None):
    """New FLOAT auxiliary integral, using old exact source metadata only."""
    import numpy as np
    from mobius_transport_source_059 import _band_empty
    meter=meter or Meter()
    if type(N) is not int or not 2<=N<=262144:raise ValueError('bounded integer diagnostic scale')
    if type(degree) is not int or not 4<=degree<=32:raise ValueError('bounded new quadrature degree')
    alpha,gamma,tau=(_q(parameters[k]) for k in ('alpha','gamma','tau'))
    theta,rho=_q(head_theta),_q(exit_rho)
    if not 0<=theta<=Q(1,2) or not 0<=rho<=Q(3,4):raise ValueError('paid cofactor cutoffs')
    table=prefix_table(tokens,kernels,meter);D=max(1,4*N//parameters['p'])
    if table['rows'] and table['rows'][-1]['d']>D:raise ValueError('complete source horizon')
    K=min(D//2,floor_power(N,exit_rho,meter))
    logY=float(theta)*log(N);Y=exp(logY);a=min(Y,D);b=max(a,D-K)
    result={'N':N,'horizon':D,'exit_width':K,'head_cut_float':a,'core_end_float':b,
            'prefix_table':table,'new_auxiliary_integral':True,'descriptive_float_only':True,
            'head_float':0.0,'core_float':0.0,'exit_float':0.0,'terminal_float':0.0,
            'total_float':0.0,'prefix_root_candidates':0,'interior_breakpoints':0,'quadrature_nodes':0,
            'uniform_core_bound_proved':False,'RH_proved':False}
    if not table['rows']:result['empty_source']=True;return result
    # The existing helper's meter also records a primitive estimate; adapt it
    # locally without calling any scientific source or kernel evaluator.
    class BandMeter:
        primitives={'exact_power_bits':0}
        def charge(self,n=1):meter.charge(n)
    if _band_empty(N,gamma,tau,BandMeter()):result['empty_band']=True;return result
    lo=exp(-float(gamma)*log(N));hi=float(tau)
    if not 0<lo<hi:raise ArithmeticError('nonempty FLOAT band must agree with exact gate')
    bases=table['bases'];logratio=log1p((bases[1]-bases[0])/bases[0])
    ratios=root_ratios(table,meter);points=[lo,hi]
    for ratio in ratios:
        t=-log1p(float(ratio-1))/logratio
        if lo<t<hi:points.append(t)
    points=sorted(set(points));result['prefix_root_candidates']=len(ratios)
    result['interior_breakpoints']=len(points)-2
    nodes,weights=np.polynomial.legendre.leggauss(degree);meter.charge(degree**3+32*degree)
    count=degree*(len(points)-1)
    meter.reserve(1024+len(table['rows'])*NODE_BATCH*80+count*128)
    ts=[];ws=[]
    for left,right in zip(points,points[1:]):
        ts.extend((nodes*(right-left)/2+(left+right)/2).tolist())
        ws.extend((weights*(right-left)/2).tolist())
    result['quadrature_nodes']=count
    ds=np.array([r['d'] for r in table['rows']],dtype=np.float64)
    coeff=np.array([r['coefficients'] for r in table['rows']],dtype=np.int64)
    left_logs=np.log(ds);right_logs=np.log(np.r_[ds[1:],float(D)])
    # Three real-y intervals partition every prefix-constant segment.
    ranges=[]
    for lower,upper in ((1.0,a),(a,b),(b,float(D))):
        lower_logs=np.maximum(left_logs,log(max(1.0,lower)))
        widths=np.maximum(0.0,np.minimum(right_logs,log(max(1.0,upper)))-lower_logs)
        ranges.append((lower_logs,widths))
    totals=[[],[],[],[]]
    for start in range(0,count,NODE_BATCH):
        t=np.asarray(ts[start:start+NODE_BATCH]);weight=np.asarray(ws[start:start+NODE_BATCH])
        masses=np.exp(-log(bases[0])*t)[None,:]*(coeff[:,0,None]+coeff[:,1,None]
                    +coeff[:,1,None]*np.expm1(-logratio*t)[None,:])
        absolute=np.abs(masses);G=np.ones(len(t))
        for prime in parameters['primes']:G*=-np.expm1(-log(prime)*t)
        quadrature=weight*exp(-lgamma(1-float(alpha)))*G*np.power(t,-1-float(alpha))
        for index,(lower_logs,widths) in enumerate(ranges):
            gaps=np.exp(-lower_logs[:,None]*t[None,:])*(-np.expm1(-widths[:,None]*t[None,:]))
            totals[index].append(float(np.dot(quadrature,np.sum(absolute*gaps,axis=0))))
        totals[3].append(float(np.dot(quadrature,absolute[-1]*np.exp(-log(D)*t))))
        meter.charge(256*len(ds)*len(t)+64*len(t)*len(parameters['primes']))
    costs=[fsum(row) for row in totals]
    if any(not isfinite(x) or x<0 for x in costs):raise ArithmeticError('finite nonnegative descriptive costs')
    for key,value in zip(('head_float','core_float','exit_float','terminal_float'),costs):result[key]=value
    result['total_float']=fsum(costs)
    return result
