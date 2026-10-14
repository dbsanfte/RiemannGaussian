"""Discover scale-uniform signed exchange laws from a generic step profile.

The learner uses multiplier factorizations, geometric cells and exact capacity
states. It does not evaluate mu at source-scale indices or fit a growth rate.
"""
from fractions import Fraction as Q
from math import gcd, isqrt, isfinite
import warnings
import numpy as np
from scipy.optimize import linprog, OptimizeWarning
from scipy.sparse import csr_matrix
from prime_transfer_algebra_058 import Meter
from mobius_convolution_scale_069 import rational

SCHEMA='mobius-uniform-exchange-law-v1'
GRID=1<<20
MAX_CANDIDATES=20000
MAX_ROWS=200000
SOURCE_PROFILE=[dict(lo='8',hi='10',value='1'),dict(lo='16',hi='20',value='-1')]


def profile_checked(profile):
    if type(profile) is not list or not 1<=len(profile)<=16:raise ValueError('bounded nonempty step profile')
    end=Q(0); parsed=[]
    for band in profile:
        if type(band) is not dict or set(band)!={'lo','hi','value'}:raise ValueError('complete profile band')
        lo,hi,value=(rational(band[k]) for k in ('lo','hi','value'))
        if not end<=lo<hi<=100 or not value:raise ValueError('ordered disjoint nonzero profile bands')
        parsed.append((lo,hi,value));end=hi
    return parsed


def multiplier_dictionary(cap,meter):
    if type(cap) is not int or not 2<=cap<=23:raise ValueError('explicit bounded exchange dictionary')
    primes=[]; entries={1:(1,0)}
    for n in range(2,cap+1):
        rest=n;mask=0;parity=1;squarefree=True
        for i,p in enumerate(primes):
            meter.charge(4)
            if rest%p==0:
                rest//=p;mask|=1<<i;parity=-parity
                if rest%p==0:squarefree=False;break
        if not squarefree:continue
        if rest>1:
            if rest not in primes:primes.append(rest)
            mask|=1<<primes.index(rest);parity=-parity
        entries[n]=(parity,mask)
    if len(primes)>9:raise MemoryError('exact divisibility state capacity')
    return primes,entries


def enumerate_families(profile,cap,meter):
    bands=profile_checked(profile);primes,entries=multiplier_dictionary(cap,meter)
    families=[]
    for a,(sa,ma) in sorted(entries.items()):
        for b,(sb,mb) in sorted(entries.items()):
            if b<=a or gcd(a,b)!=1:continue
            density=Q(1)
            for i,p in enumerate(primes):
                if (ma|mb)&(1<<i):density*=Q(p,p+1)
            for la,ha,va in bands:
                for lb,hb,vb in bands:
                    lo,hi=max(la/a,lb/b),min(ha/a,hb/b)
                    gain=abs(va)+abs(vb)-abs(sa*va+sb*vb)
                    meter.charge(32)
                    if lo<hi and gain>0:
                        families.append(dict(a=a,b=b,lo=str(lo),hi=str(hi),left_value=str(va),
                            right_value=str(vb),gain=str(gain),density_ratio=str(density)))
                        if len(families)>MAX_CANDIDATES:raise MemoryError('complete family capacity')
    return primes,entries,families


def capacity_rows(primes,entries,families,meter):
    points=set();decoded=[]
    for f in families:
        a,b=f['a'],f['b'];lo,hi=Q(f['lo']),Q(f['hi']);ma,mb=entries[a][1],entries[b][1]
        ends=(a*lo,a*hi,b*lo,b*hi)
        points.update(ends);decoded.append((*ends,ma,mb,ma|mb))
    points=sorted(points);patterns=set();states=range(1<<len(primes))
    for left,right in zip(points,points[1:]):
        x=(left+right)/2
        active=[(i,ma,mb,m,la<x<=ha,lb<x<=hb) for i,(la,ha,lb,hb,ma,mb,m) in enumerate(decoded)
                if la<x<=ha or lb<x<=hb]
        for state in states:
            pattern=tuple(i for i,ma,mb,m,ina,inb in active
                          if (ina and state&m==ma) or (inb and state&m==mb))
            if pattern:patterns.add(pattern)
            meter.charge(8*len(active)+4)
        if len(patterns)>MAX_ROWS:raise MemoryError('complete capacity-pattern limit')
        meter.reserve(16*1024**2+512*len(families)+512*sum(len(p)+1 for p in patterns))
    return [list(p) for p in sorted(patterns)]


def root_upper(value):
    value=Q(value)
    if value<0:raise ValueError('nonnegative radical')
    target=value.numerator*GRID*GRID; den=value.denominator
    if max(target.bit_length(),den.bit_length())>100000:raise OverflowError('root enclosure bit capacity')
    n=isqrt(target//den)
    if n*n*den<target:n+=1
    return Q(n,GRID)


def prices(profile,entries,families,rows,nums,den,dual_nums,meter):
    lambdas=[Q(n,den) for n in nums];dual=[Q(n,GRID) for n in dual_nums]
    if any(v<0 or v>1 for v in lambdas) or any(v<0 for v in dual):raise ValueError('nonnegative bounded allocation')
    if any(sum(nums[i] for i in r)>den for r in rows):raise ValueError('all-scale capacity violation')
    rewards=[Q(f['gain'])*Q(f['density_ratio'])*(Q(f['hi'])-Q(f['lo'])) for f in families]
    column=[Q(0)]*len(families)
    for r,y in zip(rows,dual):
        for i in r:column[i]+=y;meter.charge(8)
    objective=sum((v*w for v,w in zip(lambdas,rewards)),Q(0))
    upper=sum(dual,Q(0))+sum((max(w-y,0) for w,y in zip(rewards,column)),Q(0))
    if upper<objective:raise ArithmeticError('exact weak duality')
    baseline=sum((abs(Q(p['value']))*(Q(p['hi'])-Q(p['lo'])) for p in profile),Q(0))
    error=sum((3*abs(Q(p['value']))*(root_upper(p['hi'])+root_upper(p['lo'])) for p in profile),Q(0))
    for v,f in zip(lambdas,families):
        count=(entries[f['a']][1]|entries[f['b']][1]).bit_count()
        error+=v*Q(f['gain'])*(2**count+2)*(root_upper(f['hi'])+root_upper(f['lo']))
        meter.charge(40)
    return dict(objective_gain=str(objective),objective_upper=str(upper),
        leading_upper=str(baseline-objective),leading_lower=str(baseline-upper),sqrt_error_upper=str(error))


def construct(profile,cap,meter=None):
    meter=Meter(cap=300_000_000_000) if meter is None else meter
    primes,entries,families=enumerate_families(profile,cap,meter)
    rows=capacity_rows(primes,entries,families,meter);m,n=len(rows),len(families)
    nums=[0]*n;ys=[0]*m;den=GRID
    solver=dict(status='empty_dictionary',iterations=0)
    if n:
        rewards=[Q(f['gain'])*Q(f['density_ratio'])*(Q(f['hi'])-Q(f['lo'])) for f in families]
        indices=[];indptr=[0]
        for r in rows:indices.extend(r);indptr.append(len(indices))
        meter.reserve(32*1024**2+256*(len(indices)+m+n))
        matrix=csr_matrix((np.ones(len(indices)),np.array(indices),np.array(indptr)),shape=(m,n))
        with warnings.catch_warnings():
            warnings.simplefilter('ignore',OptimizeWarning)
            res=linprog(-np.array([float(v) for v in rewards]),A_ub=matrix,b_ub=np.ones(m),
                bounds=(0,1),method='highs',options={'threads':1,'time_limit':30.0})
        solver=dict(status='proposal_accepted' if res.success else 'failed_zero_fallback',
                    iterations=int(res.nit or 0),message=str(res.message))
        meter.charge(100*(len(indices)+m+n)*(solver['iterations']+1))
        if res.success:
            if not all(isfinite(float(v)) for v in res.x):raise ValueError('finite primal proposals')
            nums=[max(0,min(GRID,int(float(v)*GRID))) for v in res.x]
            den=max(GRID,max((sum(nums[i] for i in r) for r in rows),default=0))
            for i,v in enumerate(-res.ineqlin.marginals):
                if not isfinite(float(v)):raise ValueError('finite dual proposals')
                f=Q(float(max(0,v)))*GRID
                ys[i]=(f.numerator+f.denominator-1)//f.denominator
    calculated=prices(profile,entries,families,rows,nums,den,ys,meter)
    if Q(calculated['leading_upper'])<0:raise ArithmeticError('positive source density forbids negative price')
    return dict(schema=SCHEMA,profile=profile,cap=cap,primes=primes,candidates=families,capacity_rows=rows,
        lambda_denominator=den,lambda_numerators=nums,dual_denominator=GRID,dual_numerators=ys,
        **calculated,selected_family_indices=[i for i,v in enumerate(nums) if v],solver=solver,
        uniform_profile_bound_proved=True,sublinear_profile_bound_proved=Q(calculated['leading_upper'])==0,
        uniform_head_bound_proved=False,RH_proved=False)
