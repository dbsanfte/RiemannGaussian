"""Independent dense divisor completion082. Squarefree counts, never mu signs.
Frozen073 rational/root primitives are reused; no producer or source evaluator imports.
"""
from fractions import Fraction as Q
from array import array
from math import isqrt,gcd
from bisect import bisect_left
from check_mobius_prime_storage_073 import (AdmissionError,ResourceLimit,_rational,_add,_mul,_int_mul,_power_target,_integer_root)
MAX_HORIZON=4000000
MAX_GROUPS=1024
MAX_PROFILES=32
MAX_KERNEL=128
MAX_RAYS=10000
MEMORY=4*1024**3
class Meter:
    def __init__(self,limit=300000000000):self.ops,self.limit,self.peak_bytes=0,limit,0
    def charge(self,n=1):
        self.ops+=n
        if self.ops>self.limit:raise ResourceLimit('work limit exceeded')
    def reserve(self,n):
        self.peak_bytes=max(self.peak_bytes,n)
        if n>MEMORY:raise ResourceLimit('prospective memory exceeds4GiB')
def integer(v,name,lo,hi):
    if type(v)is not int or not lo<=v<=hi:raise AdmissionError(name+' integer domain')
    return v
def parse_program(raw,meter=None):
    m=meter or Meter();keys={'schema','kernel','memory','rays','drift_multiplier','profiles','theta','gram_weights'}
    if type(raw)is not dict or set(raw)!=keys or raw['schema']!='dense-divisor-completion-v1':raise AdmissionError('exact dense program schema required')
    depth=integer(raw['memory'],'memory',1,3)
    if type(raw['kernel'])is not list or not 1<=len(raw['kernel'])<=MAX_KERNEL:raise AdmissionError('nonempty bounded kernel')
    if type(raw['profiles'])is not list or len(raw['profiles'])>MAX_PROFILES:raise AdmissionError('profile gate')
    if type(raw['rays'])is not list or len(raw['rays'])>MAX_RAYS:raise AdmissionError('ray gate')
    m.reserve(16384+4096*(len(raw['kernel'])+len(raw['rays'])+len(raw['profiles'])))
    kernel=[];prev=0
    for row in raw['kernel']:
        if type(row)is not dict or set(row)!={'divisor','weight'}:raise AdmissionError('kernel entry schema')
        d=integer(row['divisor'],'divisor',1,(1<<4096)-1);w=_rational(row['weight'],'weight',m)
        if d<=prev or not w:raise AdmissionError('kernel sorted distinct nonzero required')
        kernel.append((d,w));prev=d
    rays=[]
    for row in raw['rays']:
        if type(row)is not dict or set(row)!={'a','weight'} or type(row['a'])is not list or len(row['a'])!=depth:raise AdmissionError('ray schema')
        a=tuple(_rational(x,'ray coefficient',m)for x in row['a']);w=_rational(row['weight'],'ray weight',m)
        if w<=0:raise AdmissionError('positive ray weight required')
        rays.append((a,w))
    r=_rational(raw['drift_multiplier'],'drift multiplier',m)
    if not 1<=r<=2:raise AdmissionError('drift multiplier domain')
    profiles=[]
    for row in raw['profiles']:
        if type(row)is not dict or set(row)!={'scale','eta'}:raise AdmissionError('profile schema')
        scale=_rational(row['scale'],'scale',m);eta=_rational(row['eta'],'eta',m)
        if scale<=0 or not 0<eta<=1:raise AdmissionError('positive scale,0<eta<=1 required')
        profiles.append((scale,eta))
    dim=depth+1
    if type(raw['theta'])is not list or len(raw['theta'])!=len(profiles):raise AdmissionError('theta shape')
    theta=[]
    for row in raw['theta']:
        if type(row)is not list or len(row)!=dim:raise AdmissionError('theta row shape')
        values=tuple(_rational(x,'theta',m)for x in row)
        if any(abs(x)>16 for x in values):raise AdmissionError('theta grammar bound16')
        theta.append(values)
    if type(raw['gram_weights'])is not list or len(raw['gram_weights'])!=dim+len(profiles):raise AdmissionError('Gram weight shape')
    gram=tuple(_rational(x,'Gram weight',m)for x in raw['gram_weights'])
    if any(not 0<=x<=16 for x in gram):raise AdmissionError('Gram weights must be0..16')
    return dict(kernel=tuple(kernel),memory=depth,rays=tuple(rays),drift_multiplier=r,profiles=tuple(profiles),theta=tuple(theta),gram_weights=gram)
def drift_matrix(p,m):
    d=p['memory'];H=[[Q(int(i==j==0))for j in range(d)]for i in range(d)]
    for a,w in p['rays']:
        for i in range(d):
            for j in range(d):H[i][j]=_add(H[i][j],_mul(w,_mul(a[i],a[j],m),m),m)
    T=[[Q(0)for j in range(d+1)]for i in range(d+1)]
    for i in range(d):
        for j in range(d):T[i][j]=_add(T[i][j],H[i][j],m);T[i+1][j+1]=_add(T[i+1][j+1],-_mul(p['drift_multiplier'],H[i][j],m),m)
    return T
def profile_cut(u,N,scale,eta,m):
    # floor(scale*u^eta), with all powers prospectively gated by frozen073.
    a=_power_target(scale.numerator,eta.denominator,1,0,m)
    b=_power_target(scale.denominator,eta.denominator,1,0,m)
    c=_power_target(u,eta.numerator,1,0,m)
    return min(N,_integer_root(_int_mul(a,c,m)//b,eta.denominator,m))
def squarefree_prefix(N,m):
    m.reserve(16384+8*(N+1));m.charge(N+1)
    # Prime Eratosthenes to sqrtN, then strike p^2 multiples. No mu/lpf arrays.
    lim=isqrt(N);composite=bytearray(lim+1);sf=bytearray(b'\1')*(N+1);sf[0]=0
    for p in range(2,lim+1):
        m.charge()
        if composite[p]:continue
        if p*p<=lim:
            count=(lim-p*p)//p+1;m.charge(count);composite[p*p:lim+1:p]=b'\1'*count
        step=p*p;count=N//step;m.charge(count);sf[step:N+1:step]=b'\0'*count
    prefix=array('I',[0])*(N+1);total=0
    for n in range(1,N+1):total+=sf[n];prefix[n]=total
    m.charge(N);return prefix

def build_model(program,u,meter=None):
    """Raising API; exact model. Groups global lexicographic feature tuples."""
    m=meter or Meter();p=parse_program(program,m);integer(u,'u',1,(1<<4096)-1)
    N=u//p['kernel'][0][0]
    if N>MAX_HORIZON:raise ResourceLimit('source horizon exceeds4000000 before allocation')
    dim=p['memory']+1;T=drift_matrix(p,m)
    cuts=tuple(profile_cut(u,N,s,e,m)for s,e in p['profiles'])
    # Common denominator makes canonical global tuple ordering rational-exact.
    denominator=1
    for d,w in p['kernel']:denominator=_int_mul(denominator//gcd(denominator,w.denominator),w.denominator,m)
    sourceevents=[];breaks={0,N}
    if N:breaks.add(1)
    for i in range(dim):
        events={}
        for d,w in p['kernel']:
            end=min(N,u//((1<<i)*d));events[end]=events.get(end,0)+w.numerator*(denominator//w.denominator)
            breaks.add(end)
        endpoints=sorted(events);values=[];running=0
        for e in reversed(endpoints):running+=events[e];values.append(running)
        sourceevents.append((endpoints,list(reversed(values))))
    for K in cuts:
        n=1
        while n<=K:
            q=K//n;right=K//q;breaks.add(right);n=right+1;m.charge()
    breaklist=sorted(breaks);m.reserve(16384+8*(N+1)+1024*len(breaklist)*(dim+len(cuts)))
    prefix=squarefree_prefix(N,m);counts={}
    for left,right in zip(breaklist,breaklist[1:]):
        count=int(prefix[right]-prefix[left]);m.charge()
        if not count:continue
        n=left+1;features=[]
        for endpoints,values in sourceevents:
            index=bisect_left(endpoints,n);features.append(Q(values[index],denominator)if index<len(endpoints)else Q(0))
        features.extend(Q(K//n-int(n==1))if K else Q(0)for K in cuts)
        key=tuple(features);counts[key]=counts.get(key,0)+count
        if len(counts)>MAX_GROUPS:raise ResourceLimit('complete group matrix exceeds1024 groups')
    groups=tuple(sorted(counts));multiplicities=tuple(counts[g]for g in groups)
    return dict(program=p,u=u,N=N,cuts=cuts,features=groups,counts=multiplicities,squarefree_count=int(prefix[N]),T=T,group_count=len(groups),normalization='sum_mu/group_squarefree_count')

def _matrix_budget(model,m):
    p=model['program'];vals=[v for row in model['T']for v in row]+[v for row in p['theta']for v in row]+list(p['gram_weights'])+[v for row in model['features']for v in row]
    # Denominators of every summand divide common^3. This deliberately covers
    # mixed T*f*f, theta*C*f, Gram*f*f and addition without repeated-LCM growth.
    common=1;max_num=1
    for v in vals:
        common=_int_mul(common//gcd(common,v.denominator),v.denominator,m);max_num=max(max_num,abs(v.numerator).bit_length())
    terms=(p['memory']+1)**2+2*len(p['profiles'])*(p['memory']+1)+len(p['gram_weights'])
    bits=3*(common.bit_length()+max_num)+2*max(1,model['N'].bit_length())+max(1,terms.bit_length())+8
    if bits>100000:raise ResourceLimit('prospective matrix rational bit gate')
    n=model['group_count'];m.reserve(16384+8*(model['N']+1)+n*n*(256+bits)+n*(512+bits))
    m.charge(n*n*max(1,terms));return bits

def corrected_matrix(model,meter=None):
    m=meter or Meter();_matrix_budget(model,m);p=model['program'];dim=p['memory']+1;features=model['features'];counts=model['counts'];T=model['T'];n=len(features)
    A=[[Q(0)for _ in range(n)]for _ in range(n)]
    for g in range(n):
        x=features[g]
        for h in range(g,n):
            y=features[h];value=Q(0)
            for i in range(dim):
                for j in range(dim):value=_add(value,_mul(T[i][j],_mul(x[i],y[j],m),m),m)
            for k,theta in enumerate(p['theta']):
                for i,t in enumerate(theta):
                    term=_add(_mul(x[dim+k],y[i],m),_mul(x[i],y[dim+k],m),m)
                    value=_add(value,_mul(t,term,m),m)
            for i,w in enumerate(p['gram_weights']):value=_add(value,_mul(w,_mul(x[i],y[i],m),m),m)
            value=_mul(value,Q(counts[g]*counts[h]),m);A[g][h]=A[h][g]=value
    return A

def finish(out,m,error=None):
    if error is not None:
        out.update(status='INVALID',reason=str(error),resource_limit=isinstance(error,ResourceLimit))
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_original_source_bound_proved=False,uniform_source_bound_proved=False,uniform_growth_proved=False,RH_proved=False,source_kernel_binding_still_required=True)
    return out

def verify_certificate(program,u,certificate,meter=None):
    m=meter or Meter();out={}
    try:
        model=build_model(program,u,m)
        if type(certificate)is not dict or set(certificate)!={'group_count','squarefree_count','price','row_prices'}:raise AdmissionError('exact dense certificate schema')
        integer(certificate['group_count'],'group_count',0,MAX_GROUPS);integer(certificate['squarefree_count'],'squarefree_count',0,MAX_HORIZON)
        if certificate['group_count']!=model['group_count'] or certificate['squarefree_count']!=model['squarefree_count']:raise AdmissionError('complete squarefree groups/count mismatch')
        if type(certificate['row_prices'])is not list or len(certificate['row_prices'])!=model['group_count']:raise AdmissionError('row price shape')
        supplied=tuple(_rational(v,'row price',m)for v in certificate['row_prices']);price=_rational(certificate['price'],'price',m)
        A=corrected_matrix(model,m);rows=[]
        for g,row in enumerate(A):
            val=row[g]
            for h,x in enumerate(row):
                if h!=g:val=_add(val,abs(x),m)
            rows.append(max(Q(0),val))
        total=Q(0)
        for v in rows:total=_add(total,v,m)
        if tuple(rows)!=supplied or total!=price:raise AdmissionError('independent dense SDD price mismatch')
        out.update(status='VERIFIED_FINITE_DENSE_UPPER_BOUND',u=u,horizon=model['N'],group_count=model['group_count'],squarefree_count=model['squarefree_count'],profile_cuts=list(model['cuts']),price=str(total),row_prices=[str(v)for v in rows],complete_target_admitted=True,prime_edges_retained=True,unit_included=model['N']>=1,divisor_zero_identities_verified=True,positive_Gram_cost_retained=True,proof='diag(row_prices)-corrected_A is symmetric diagonally dominant with nonnegative diagonal; |sum_mu/count|<=1',growing_profiles_identity_scope='Every u with these complete profiles; uniform price law unpaid')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return finish(out,m,e)
    return finish(out,m)

def verify_price_dual(program,u,certificate,meter=None):
    """Exact finite lower bound for minimum SDD price over the entire box grammar.

    lambda pairs with diagonal; nu pairs ONCE with A_gh for g<h. This is not
    a lower bound for actual mu drift, and negative lower bounds are valid.
    """
    m=meter or Meter();out={}
    try:
        model=build_model(program,u,m);p=model['program'];G=model['group_count'];pairs=G*(G-1)//2
        if type(certificate)is not dict or set(certificate)!={'lambda','nu','lower_bound'}:raise AdmissionError('exact price dual schema')
        if type(certificate['lambda'])is not list or len(certificate['lambda'])!=G or type(certificate['nu'])is not list or len(certificate['nu'])!=pairs:raise AdmissionError('complete dual lambda/nu shape')
        # Inspect actual incoming strings BEFORE allocating parsed nu fractions.
        rawbytes=16384
        for v in (*certificate['lambda'],certificate['lower_bound']):
            if type(v)is not str:raise AdmissionError('dual rational strings required')
            rawbytes+=512+8*len(v)
        for v in certificate['nu']:
            if type(v)is not str:raise AdmissionError('dual rational strings required')
            rawbytes+=512+8*len(v)
        m.reserve(rawbytes+8*(model['N']+1));m.charge(G+pairs)
        lam=tuple(_rational(v,'lambda',m)for v in certificate['lambda'])
        if any(not 0<=v<=1 for v in lam):raise AdmissionError('dual lambda0..1 required')
        nu=tuple(_rational(v,'nu',m)for v in certificate['nu']);supplied=_rational(certificate['lower_bound'],'lower_bound',m)
        index=0
        for g in range(G):
            for h in range(g+1,G):
                if abs(nu[index])>lam[g]+lam[h]:raise AdmissionError('dual offdiagonal feasibility failed')
                index+=1
        dim=p['memory']+1;full=dim+len(p['profiles'])
        needed={(i,j)for i in range(dim)for j in range(i,dim)}
        needed.update((i,dim+k)for k in range(len(p['profiles']))for i in range(dim));needed.update((i,i)for i in range(full))
        ordered=sorted(needed);totals={key:Q(0)for key in ordered}
        # Sufficient rational contraction budget uses actual common denominators.
        common=1;largest=1
        for v in (*lam,*nu,*(x for f in model['features']for x in f)):
            common=_int_mul(common//gcd(common,v.denominator),v.denominator,m);largest=max(largest,abs(v.numerator).bit_length())
        bits=3*(common.bit_length()+largest)+2*max(1,model['N'].bit_length())+max(1,(G+pairs).bit_length())+8
        if bits>100000:raise ResourceLimit('prospective dual contraction rational bit gate')
        m.reserve(rawbytes+8*(model['N']+1)+len(ordered)*(512+bits));m.charge(max(1,G+pairs)*max(1,len(ordered)))
        features=model['features'];counts=model['counts']
        for g in range(G):
            coeff=_mul(lam[g],Q(counts[g]**2),m);x=features[g]
            if coeff:
                for i,j in ordered:totals[i,j]=_add(totals[i,j],_mul(coeff,_mul(x[i],x[j],m),m),m)
        index=0
        for g in range(G):
            x=features[g]
            for h in range(g+1,G):
                coeff=_mul(nu[index],Q(counts[g]*counts[h],2),m);index+=1;y=features[h]
                if not coeff:continue
                for i,j in ordered:
                    value=_add(_mul(x[i],y[j],m),_mul(x[j],y[i],m),m)
                    totals[i,j]=_add(totals[i,j],_mul(coeff,value,m),m)
        base=Q(0);T=model['T']
        for i in range(dim):
            for j in range(i,dim):base=_add(base,_mul(T[i][j],_mul(Q(1 if i==j else 2),totals[i,j],m),m),m)
        zero_values=[_mul(Q(2),totals[i,dim+k],m)for k in range(len(p['profiles']))for i in range(dim)]
        gram_values=[totals[i,i]for i in range(full)]
        lower=base
        for value in zero_values:lower=_add(lower,-_mul(Q(16),abs(value),m),m)
        for value in gram_values:lower=_add(lower,_mul(Q(16),min(Q(0),value),m),m)
        if lower!=supplied:raise AdmissionError('independent grammar dual lower bound mismatch')
        out.update(status='VERIFIED_FINITE_GRAMMAR_PRICE_LOWER_BOUND',u=u,horizon=model['N'],group_count=G,squarefree_count=model['squarefree_count'],lower_bound=str(lower),base_functional=str(base),zero_template_functionals=[str(v)for v in zero_values],gram_template_functionals=[str(v)for v in gram_values],all_theta_box=[-16,16],all_gram_box=[0,16],actual_parameter_values_irrelevant=True,actual_signed_drift_lower_bound_proved=False,uniform_price_lower_bound_proved=False,complete_geometry_admitted=True,proof='Feasible diagonal/offdiagonal dual gives L(A)<=sum max(0,Agg+offdiag_l1); minimize this linear functional independently over each box parameter.')
    except (ValueError,TypeError,KeyError,OverflowError)as e:return finish(out,m,e)
    return finish(out,m)
