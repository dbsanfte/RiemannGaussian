"""Explicit, scale-independent recipes for the unpaid short repair.

Each recipe is an algorithm for every H, not a newly fitted LP vector.
Its exact reconstruction identity does not establish uniform budget growth.
"""
from fractions import Fraction as Q
from math import gcd,prod

from prime_transfer_algebra_058 import Meter
from mobius_prefix_completion_062 import ordinary_mu,weight,indicators

RULES=('raw','zero','left','right','linear','reciprocal_linear','core','core_inverse')


def short_residuals(base,meter=None):
    meter=Meter() if meter is None else meter
    params=base['parameters'];N,y,H=(base[k] for k in ('N','y','H'))
    p,q=params['p'],params['q'];Xs=base['horizons']
    if any(X<=H for X in Xs):raise ValueError('generic base must contain only long horizons')
    cs=[[Q(x) for x in row] for row in base['coefficients']]
    result=[[],[]]
    for d in range(1,H+1):
        a=weight(N,p,d) if d<=y else 0;b=weight(N,q,d) if d<=y else 0
        floors=[X//d for X in Xs]
        for e,r in enumerate((Q(p,q),Q(1))):
            result[e].append(Q(a)-r*b-sum((c*f for c,f in zip(cs[e],floors)),Q(0)))
            meter.charge(16*len(Xs)+20)
    return result


def fill_rows(values,primes,rule,meter=None):
    meter=Meter() if meter is None else meter
    if rule not in RULES:raise ValueError('registered analytic fill recipe')
    H=len(values);R=prod(primes);values=list(map(Q,values));out=list(values)
    nodes=[d for d in range(1,H+1) if gcd(d,R)==1]+[H+1]
    pos=0
    for d in range(1,H+1):
        meter.charge(16)
        while pos+1<len(nodes) and nodes[pos+1]<=d:pos+=1
        if gcd(d,R)==1 or rule=='raw':continue
        if rule=='zero':out[d-1]=Q(0);continue
        if rule in ('core','core_inverse'):
            core=d
            for p in primes:
                while core%p==0:core//=p;meter.charge(4)
            out[d-1]=values[core-1]/(d//core if rule=='core_inverse' else 1)
            continue
        a,b=nodes[pos],nodes[pos+1]
        left=values[a-1];right=values[b-1] if b<=H else Q(0)
        if rule=='left':out[d-1]=left
        elif rule=='right':out[d-1]=right
        elif rule=='linear':out[d-1]=(b-d)*left/(b-a)+(d-a)*right/(b-a)
        else:out[d-1]=Q(a*(b-d),d*(b-a))*left+Q(b*(d-a),d*(b-a))*right
        meter.charge(30)
    return out


def inverse_floor(values,mu,meter=None):
    """A(j)=sum_m mu(m)g(jm); c(j)=A(j)-A(j+1)."""
    meter=Meter() if meter is None else meter
    H=len(values)
    if len(mu)<=H:raise ValueError('complete inverse kernel through H')
    A=[Q(0)]*(H+2)
    for j in range(1,H+1):
        for m in range(1,H//j+1):
            A[j]+=mu[m]*values[j*m-1];meter.charge(16)
    return [A[j]-A[j+1] for j in range(1,H+1)]


def construct(base,rule,residuals=None,mu=None,meter=None):
    meter=Meter() if meter is None else meter
    H=base['H'];primes=base['parameters']['primes']
    if not 1<=H<=4096:raise OverflowError('repair support capacity')
    meter.reserve(1024*1024+4096*H)
    residuals=short_residuals(base,meter) if residuals is None else residuals
    mu=ordinary_mu(H,meter) if mu is None else mu
    filled=[fill_rows(row,primes,rule,meter) for row in residuals]
    coefficients=[inverse_floor(row,mu,meter) for row in filled]
    costs=[sum(map(abs,row),Q(0)) for row in coefficients]
    repair={'schema':'mobius-short-repair-v1','primes':primes,'H':H,'rule':rule,
            'residuals':[[str(c) for c in row] for row in residuals],
            'filled':[[str(c) for c in row] for row in filled],
            'coefficients':[[str(c) for c in row] for row in coefficients],
            'coefficient_l1':[str(c) for c in costs]}
    supports=sorted(set(base['horizons'])|{j for j in range(1,H+1) if any(row[j-1] for row in coefficients)})
    maps=[{X:Q(c) for X,c in zip(base['horizons'],row)} for row in base['coefficients']]
    for e in range(2):
        for j,c in enumerate(coefficients[e],1):
            if c:maps[e][j]=c
    combined=[[maps[e].get(X,Q(0)) for X in supports] for e in range(2)]
    new_budget=max(sum(map(abs,row),Q(0)) for row in combined)
    new={**base,'horizons':supports,'coefficients':[[str(c) for c in row] for row in combined],
         'budget':str(new_budget)}
    return {'rule':rule,'repair':repair,'completion':new,
        'base_budget':base['budget'],'new_budget':str(new_budget),
        'new_short_residual_claim':'zero on every coprime row; requires independent whole-certificate admission',
        'formula_valid_for_arbitrary_H':True,'uniform_growth_proved':False}


def discover(base,meter=None):
    meter=Meter() if meter is None else meter
    residuals=short_residuals(base,meter);mu=ordinary_mu(base['H'],meter)
    rows=[construct(base,rule,residuals,mu,meter) for rule in RULES]
    chosen=min(rows,key=lambda row:(Q(row['new_budget']),RULES.index(row['rule'])))
    return {'N':base['N'],'y':base['y'],'H':base['H'],'base_budget':base['budget'],
        'candidates':rows,'selected_rule':chosen['rule'],'selected_budget':chosen['new_budget'],
        'uniform_budget_growth_proved':False,'new_LP_used':False}


def quadratic_lift(base,rule,repair,meter=None):
    """Expose c=Delta D(u) P(f-G u), with u the SAME ordinary mu sequence.

    G is made without any arithmetic signs. Its rows are indexed by short
    d and its columns by the inverse index ell. Keeping the factorization
    avoids materializing one dense quadratic matrix for each repair j.
    """
    meter=Meter() if meter is None else meter
    N,y,H=(base[k] for k in ('N','y','H'));params=base['parameters']
    p,q=params['p'],params['q'];K=y//(H+1);radius=max(H,K)
    meter.reserve(1024*1024+2048*H*max(1,K))
    gs=[[[Q(0) for _ in range(K)] for _ in range(H)] for _ in range(2)]
    for channel,b in enumerate((p,q)):
        thresholds={}
        for factor,a in ((4,1),(2,-3),(1,2)):
            for T,multiplicity in indicators(factor*N//b,y,H,meter).items():
                thresholds[T]=thresholds.get(T,0)+a*multiplicity
        for T,a in thresholds.items():
            if not a:continue
            for ell in range(1,T//(H+1)+1):
                X=T//ell
                for d in range(1,H+1):
                    gs[channel][d-1][ell-1]+=a*(X//d);meter.charge(12)
    u=ordinary_mu(radius,meter);linear=[];kernels=[]
    for e,r in enumerate((Q(p,q),Q(1))):
        f=[Q(weight(N,p,d))-r*weight(N,q,d) if d<=y else Q(0) for d in range(1,H+1)]
        pf=fill_rows(f,params['primes'],rule,meter);pg=[[Q(0)]*K for _ in range(H)]
        for ell in range(K):
            column=[gs[0][d][ell]-r*gs[1][d][ell] for d in range(H)]
            filled=fill_rows(column,params['primes'],rule,meter)
            for d,value in enumerate(filled):pg[d][ell]=value
        reconstructed=[pf[d]-sum((pg[d][ell-1]*u[ell] for ell in range(1,K+1)),Q(0)) for d in range(H)]
        meter.charge(20*H*max(1,K))
        if [str(c) for c in reconstructed]!=repair['filled'][e]:
            raise ValueError('quadratic factorization must reproduce every filled residual')
        cs=inverse_floor(reconstructed,u,meter)
        if [str(c) for c in cs]!=repair['coefficients'][e]:
            raise ValueError('quadratic factorization must reproduce every repair coefficient')
        linear.append([str(c) for c in pf]);kernels.append([[str(c) for c in row] for row in pg])
    return {'schema':'mobius-factored-quadratic-repair-v1','parameters':params,'N':N,'y':y,'H':H,
        'rule':rule,'K':K,'arithmetic_radius':radius,'ordinary_mu_through_radius':u[1:],
        'linear_terms':linear,'long_kernels_after_fill':kernels,
        'expression':'c_j=sum_(m<=H/j)u_m*[Pf-PG*u]_(j*m)-sum_(m<=H/(j+1))u_m*[Pf-PG*u]_((j+1)*m)',
        'same_u_sequence_in_both_factors':True,'arithmetic_degree_at_most':2,
        'formal_source_only_factorization_reviewed':True,
        'producer_exact_replay':True,'independent_quadratic_schema_admission':False,
        'independent_whole_completion_admission_still_required':True,
        'uniform_quadratic_variation_bound_proved':False,'RH_proved':False}
