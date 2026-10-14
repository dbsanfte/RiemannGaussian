"""Independent growing balanced-density packet algebra and uniform bound081.

Elementary squarefree-count error only; no PNT/RH or producer import. A bound
for the signed extracted packet does not bound the original residual/drift.
"""
from fractions import Fraction
import check_mobius_residual_fold_077 as F
import check_mobius_prime_mass_gate_078 as K
from check_mobius_prime_storage_073 import (AdmissionError,ResourceLimit,_rational,_add,_mul,_divide,_power_target,_integer_root,_power_compare,power_enclosure,_int_mul)
class Meter(F.Meter):pass
MAX_PRIME_HORIZON=1000000
MAX_RAYS=10000
_OMEGA_CACHE={}
_OMEGA_BYTES=0

def _done(out,m,error=None):
    if error is not None:
        out.update(status='INVALID',reason=str(error))
        if isinstance(error,ResourceLimit):out['resource_limit']=True
    out.update(ops=m.ops,peak_bytes=m.peak_bytes,uniform_original_residual_bound_proved=False,uniform_source_bound_proved=False,uniform_unlinked_correlation_proved=False,RH_proved=False,source_kernel_binding_still_required=True)
    return out

def parse_program(raw,meter=None):
    """Strict schema admission; raises on malformed/resource-unadmitted programs."""
    m=meter or Meter();keys={'schema','kernel','memory','rays','drift_multiplier','epsilon','eta','q'}
    if type(raw) is not dict or set(raw)!=keys or raw['schema']!='growing-density-packet-v1':raise AdmissionError('invalid density packet program schema')
    depth=F._integer(raw['memory'],'memory',1,3);kernel=K._kernel(raw['kernel'],m)
    if type(raw['rays']) is not list or len(raw['rays'])>MAX_RAYS:raise AdmissionError('invalid resource bounded rays')
    m.reserve(_resident()+8192*(1+len(raw['rays'])+len(kernel)))
    rays=[]
    for row in raw['rays']:
        if type(row) is not dict or set(row)!={'a','weight'} or type(row['a']) is not list or len(row['a'])!=depth:raise AdmissionError('invalid memory ray')
        weight=_rational(row['weight'],'ray weight',m);a=tuple(_rational(v,'ray coefficient',m) for v in row['a'])
        if weight<=0:raise AdmissionError('ray weights must be positive')
        rays.append((a,weight))
    r=_rational(raw['drift_multiplier'],'drift multiplier',m);eps=_rational(raw['epsilon'],'epsilon',m);eta=_rational(raw['eta'],'eta',m);q=_rational(raw['q'],'q',m)
    if not 1<=r<=2 or not 0<eps<=1 or not 0<eta<=1 or not 1<=q<2:raise AdmissionError('program exponent/drift domain')
    return {'kernel':kernel,'memory':depth,'rays':rays,'drift_multiplier':r,'epsilon':eps,'eta':eta,'q':q}

def drift_matrix(parsed,meter=None):
    m=meter or Meter();depth=parsed['memory'];H=[[Fraction(0) for _ in range(depth)] for _ in range(depth)];H[0][0]=Fraction(1)
    for a,w in parsed['rays']:
        for i in range(depth):
            for j in range(depth):H[i][j]=_add(H[i][j],_mul(w,_mul(a[i],a[j],m),m),m)
    T=[[Fraction(0) for _ in range(depth+1)] for _ in range(depth+1)]
    for i in range(depth):
        for j in range(depth):T[i][j]=_add(T[i][j],H[i][j],m);T[i+1][j+1]=_add(T[i+1][j+1],-_mul(parsed['drift_multiplier'],H[i][j],m),m)
    return H,T

def _ceil24(value,m):
    m.charge(value.numerator.bit_length()+value.denominator.bit_length())
    return Fraction(-((-value.numerator*2**24)//value.denominator),2**24)

def omega_price(epsilon,meter=None):
    """Certify2^omega(n)<=price*n^epsilon for every positive integer n."""
    global _OMEGA_BYTES
    m=meter or Meter();eps=epsilon if isinstance(epsilon,Fraction) else _rational(epsilon,'epsilon',m)
    if not 0<eps<=1:raise AdmissionError('epsilon domain')
    key=(eps,24)
    if key in _OMEGA_CACHE:
        m.reserve(_resident()+4096);m.charge();return _OMEGA_CACHE[key]
    target=_power_target(2,eps.denominator,1,0,m);horizon=_integer_root(target,eps.numerator,m)
    if horizon>MAX_PRIME_HORIZON:raise ResourceLimit('omega prime horizon exceeds1000000')
    m.reserve(_resident()+64*(horizon+1)+4096);m.charge(horizon+1)
    composite=bytearray(horizon+1);price=Fraction(1);included=[]
    for p in range(2,horizon+1):
        m.charge()
        if composite[p]:continue
        if p*p<=horizon:
            length=(horizon-p*p)//p+1;m.charge(length);composite[p*p:horizon+1:p]=b'\1'*length
        if _power_compare(p,eps.numerator,target,m)>=0:continue
        lower,_=power_enclosure(p,eps,24,m)
        if lower<=0:raise AdmissionError('positive prime-power lower bound unpaid')
        price=_ceil24(_mul(price,_divide(Fraction(2),lower,m),m),m);included.append(p)
    result={'price':price,'primes':tuple(included),'horizon':horizon};cost=512+48*len(included)+4*(price.numerator.bit_length()+price.denominator.bit_length())
    if _OMEGA_BYTES+cost>64*1024**2:_OMEGA_CACHE.clear();_OMEGA_BYTES=0
    m.reserve(_resident()+cost+64*(horizon+1)+4096);_OMEGA_CACHE[key]=result;_OMEGA_BYTES+=cost
    return result

def verify_bound(program,certificate,meter=None):
    m=meter or Meter();out={}
    try:
        parsed=parse_program(program,m);H,T=drift_matrix(parsed,m);omega=omega_price(parsed['epsilon'],m)
        total=Fraction(0)
        for w in parsed['kernel'].values():total=_add(total,abs(w),m)
        norm=Fraction(0)
        for row in T:
            for value in row:norm=_add(norm,abs(value),m)
        jump=_mul(Fraction(2),_mul(norm,_mul(total,total,m),m),m)
        constant=_mul(jump,_add(omega['price'],Fraction(2),m),m)
        exponent=_add(Fraction(1,2),_mul(parsed['eta'],_add(Fraction(3,2),_mul(Fraction(2),parsed['epsilon'],m),m),m),m)
        if type(certificate) is not dict or set(certificate)!={'omega_price','jump_price','constant','exponent'}:raise AdmissionError('exact packet bound certificate required')
        supplied={key:_rational(value,key,m) for key,value in certificate.items()}
        if supplied!={'omega_price':omega['price'],'jump_price':jump,'constant':constant,'exponent':exponent}:raise AdmissionError('independent packet price mismatch')
        if exponent>parsed['q']:
            out.update(status='UNPAID_EXPONENT',exponent=str(exponent),q=str(parsed['q']),uniform_signed_packet_bound_proved=False)
        else:out.update(status='VERIFIED_UNIFORM_SIGNED_PACKET_BOUND',uniform_signed_packet_bound_proved=True,omega_price=str(omega['price']),jump_price=str(jump),constant=str(constant),exponent=str(exponent),q=str(parsed['q']),omega_prime_horizon=omega['horizon'],omega_primes=list(omega['primes']),H=[[str(v) for v in row] for row in H],T=[[str(v) for v in row] for row in T],bound='|W(u)|<=constant*u^q for every positive integer u',balance_rule='positive min(1,N/P); negative min(1,P/N); zero1; absent bucket nonzero side0',analytic_premise='elementary squarefree coprime count error <=(2^omega(N)+2)*sqrt(x)',density_balance_admission_still_required=True,pair_compilation_admission_still_required=True,unlinked_remainder_unpaid=True)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

# Finite source/compilation caches use explicit mathematical content, never hashes.
import math
import numpy as np
import check_mobius_rough_energy_078 as A
_PAIR_CACHE={}
_PAIR_BYTES=0
_Q_CACHE={}
_Q_BYTES=0
_PREFIX=None
MAX_FINITE_PAIRS=200000
CACHE_LIMIT=64*1024**2

def _resident():
    return A._resident()+_OMEGA_BYTES+_PAIR_BYTES+_Q_BYTES+(0 if _PREFIX is None else _PREFIX.nbytes)

def _factor_primes(n,source):
    result=[]
    while n>1:
        p=int(source['least'][n]);result.append(p)
        while n%p==0:n//=p
    return result

def _program_cost(parsed):
    cost=8192
    for d,v in parsed['kernel'].items():cost+=1024+8*(d.bit_length()+v.numerator.bit_length()+v.denominator.bit_length())
    for a,w in parsed['rays']:
        for v in (*a,w):cost+=512+8*(v.numerator.bit_length()+v.denominator.bit_length())
    return cost

def _lcm(values,m):
    result=1
    for value in values:result=_int_mul(result//math.gcd(result,value),value,m)
    return result

def _pair_budget(parsed,T,label_bits,m):
    """Prospective rational/table sizes from actual LCMs; no fixedbytes/pair."""
    kernel=parsed['kernel'];n=len(kernel);dim=len(T);products=dim**2*n**2
    if products>100000:raise ResourceLimit('prospective direct pair term gate')
    kd=_lcm((v.denominator for v in kernel.values()),m);td=_lcm((v.denominator for row in T for v in row),m)
    common=_int_mul(td,_int_mul(kd,kd,m),m);divisor_lcm=_lcm(kernel,m)
    denomin_bits=common.bit_length();max_kernel_num=max((abs(v.numerator).bit_length() for v in kernel.values()),default=1);max_T_num=max((abs(v.numerator).bit_length() for row in T for v in row),default=1)
    numer_bits=min(100000,max_T_num+2*max_kernel_num+denomin_bits+products.bit_length()+2)
    index_bits=max((d.bit_length() for d in kernel),default=1)+label_bits+dim
    unique=2*dim*n
    term_cost=1024+8*(numer_bits+denomin_bits+index_bits)
    integral_den_bits=min(100000,denomin_bits+divisor_lcm.bit_length()+2*label_bits+dim)
    integral_num_bits=min(100000,numer_bits+integral_den_bits+max(1,unique).bit_length())
    value_cost=4096+8*(2*integral_num_bits+2*integral_den_bits+8*label_bits)
    key_cost=1024+_program_cost(parsed)+sum(8*(v.numerator.bit_length()+v.denominator.bit_length()) for row in T for v in row)
    return {'pair_bytes':2048+unique*term_cost+value_cost,'temporary_bytes':8192+unique*term_cost+key_cost,'products':products}

def _pair(parsed,T,a,b,m):
    global _PAIR_BYTES
    kernel=parsed['kernel'];key=(tuple(sorted(kernel.items())),tuple(tuple(row) for row in T),a,b)
    if key in _PAIR_CACHE:m.reserve(_resident()+4096);m.charge();return _PAIR_CACHE[key]
    budget=_pair_budget(parsed,T,max(a.bit_length(),b.bit_length()),m)
    m.reserve(_resident()+_program_cost(parsed)+budget['temporary_bytes']);m.charge(budget['products']);terms={}
    for i,row in enumerate(T):
        for j,t in enumerate(row):
            if not t:continue
            for dk,bk in kernel.items():
                for dl,bl in kernel.items():
                    denominator=max(a*2**i*dk,b*2**j*dl)
                    value=_mul(Fraction(2),_mul(t,_mul(bk,bl,m),m),m);new=_add(terms.get(denominator,Fraction(0)),value,m)
                    if new:terms[denominator]=new
                    else:terms.pop(denominator,None)
    integral=Fraction(0)
    for d,c in terms.items():integral=_add(integral,_divide(c,Fraction(d),m),m)
    result=(tuple(sorted(terms.items())),integral);cost=1024+256*(1+len(kernel)+len(T)**2)+sum(8*(d.bit_length()+c.numerator.bit_length()+c.denominator.bit_length()) for d,c in kernel.items())+sum(8*(v.numerator.bit_length()+v.denominator.bit_length()) for row in T for v in row)+sum(256+8*(d.bit_length()+c.numerator.bit_length()+c.denominator.bit_length()) for d,c in terms.items())
    if _PAIR_BYTES+cost>CACHE_LIMIT:_PAIR_CACHE.clear();_PAIR_BYTES=0
    m.reserve(_resident()+cost+4096)
    if cost<=CACHE_LIMIT:_PAIR_CACHE[key]=result;_PAIR_BYTES+=cost
    return result

def audit_pair(program,a,b,meter=None):
    m=meter or Meter();out={}
    try:
        parsed=parse_program(program,m);_,T=drift_matrix(parsed,m);a=F._integer(a,'a',1,A.MAX_HORIZON);b=F._integer(b,'b',a+1,A.MAX_HORIZON)
        source=A.ensure_horizon(b,m)
        if not source['mu'][a] or not source['mu'][b] or math.gcd(a,b)!=1:raise AdmissionError('coprime squarefree canonical labels required')
        terms,I=_pair(parsed,T,a,b,m);density=Fraction(1)
        for p in _factor_primes(a,source)+_factor_primes(b,source):density=_mul(density,Fraction(p,p+1),m)
        sign=int(source['mu'][a])*int(source['mu'][b]);v=_mul(Fraction(sign),_mul(density,I,m),m)
        out.update(status='VERIFIED_PAIR_KERNEL',a=a,b=b,terms=[{'denominator':d,'coefficient':str(c)} for d,c in terms],integral=str(I),mobius_sign=sign,density_factor=str(density),signed_density=str(v),finite_pair_identity_verified=True,uniform_original_residual_bound_proved=False)
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)

def _count(N,primes,x,source,m):
    """Independent square-divisor + coprimality inclusion-exclusion, not mask query."""
    global _Q_BYTES
    key=(N,x)
    if key in _Q_CACHE:m.charge();return _Q_CACHE[key]
    divisors=[(1,1)]
    for p in primes:divisors += [(d*p,-s) for d,s in divisors]
    root=math.isqrt(x);m.reserve(_resident()+256*(1+len(divisors)));m.charge((root+1)*(len(divisors)+1));count=0
    for d in range(1,root+1):
        sign=int(source['mu'][d])
        if not sign or math.gcd(d,N)!=1:continue
        quotient=x//(d*d);coprime=sum(s*(quotient//divisor) for divisor,s in divisors);count+=sign*coprime
    cost=256+8*(N.bit_length()+x.bit_length())
    if _Q_BYTES+cost>CACHE_LIMIT:_Q_CACHE.clear();_Q_BYTES=0
    m.reserve(_resident()+cost+4096);_Q_CACHE[key]=count;_Q_BYTES+=cost
    return count

def _source_prefix(horizon,m):
    global _PREFIX
    source=A.ensure_horizon(horizon,m)
    if _PREFIX is None or len(_PREFIX)<=horizon:
        m.reserve(_resident()+16*(horizon+1)+4096);m.charge(horizon+1)
        _PREFIX=source['mu'].astype(np.int64).cumsum();_PREFIX.flags.writeable=False
    return source,_PREFIX

def verify_finite(program,u,certificate,meter=None):
    m=meter or Meter();out={}
    try:
        parsed=parse_program(program,m);H,T=drift_matrix(parsed,m);u=F._integer(u,'u',1,F.MAX_PARENT)
        keys={'D','pair_count','positive_mass','negative_mass','weighted_density','packet','energy','half_energy','drift','unlinked','state','nonzero_pairs','weighted_pairs'}
        if type(certificate) is not dict or set(certificate)!=keys:raise AdmissionError('exact finite packet certificate required')
        target=_power_target(u,parsed['eta'].numerator,parsed['eta'].denominator,0,m);D=_integer_root(target,parsed['eta'].denominator,m)
        if D>A.MAX_HORIZON or D*(D-1)//2>MAX_FINITE_PAIRS:raise ResourceLimit('prospective complete ratio bank gate')
        budget=_pair_budget(parsed,T,D.bit_length(),m);prospective=(D*(D-1)//2)*(budget['products']+1);m.charge(prospective)
        horizon=max(D,max((u//d for d in parsed['kernel']),default=0))
        m.reserve(_resident()+_program_cost(parsed)+budget['temporary_bytes']+(D*(D-1)//2)*budget['pair_bytes']+64*(horizon+1)+4096)
        source,prefix=_source_prefix(horizon,m)
        depth=parsed['memory'];state=[]
        for j in range(depth+1):
            value=Fraction(0);v=u//2**j
            for d,w in parsed['kernel'].items():value=_add(value,_mul(w,Fraction(int(prefix[v//d])),m),m)
            state.append(value)
        bank=[];positive=negative=Fraction(0);nonzero=0
        for b in range(2,D+1):
            if not source['mu'][b]:continue
            for a in range(1,b):
                if not source['mu'][a] or math.gcd(a,b)!=1:continue
                terms,I=_pair(parsed,T,a,b,m);primes=_factor_primes(a,source)+_factor_primes(b,source);density=Fraction(1)
                for p in primes:density=_mul(density,Fraction(p,p+1),m)
                sign=int(source['mu'][a])*int(source['mu'][b]);v=_mul(Fraction(sign),_mul(density,I,m),m)
                if v>0:positive=_add(positive,v,m)
                elif v<0:negative=_add(negative,-v,m)
                if terms:nonzero+=1
                bank.append((a,b,terms,tuple(primes),sign,v))
        weighted_density=packet=Fraction(0);weighted=0
        for a,b,terms,primes,sign,v in bank:
            if v>0:w=min(Fraction(1),_divide(negative,positive,m))
            elif v<0:w=min(Fraction(1),_divide(positive,negative,m))
            else:w=Fraction(1)
            weighted_density=_add(weighted_density,_mul(w,v,m),m)
            if not w or not terms:continue
            weighted+=1;contribution=Fraction(0)
            for den,c in terms:contribution=_add(contribution,_mul(c,Fraction(_count(a*b,primes,u//den,source,m)),m),m)
            packet=_add(packet,_mul(w,_mul(Fraction(sign),contribution,m),m),m)
        if weighted_density:raise AdmissionError('internal exact density balance failure')
        energies=[]
        for shift in (0,1):
            energy=Fraction(0)
            for i,row in enumerate(H):
                for j,h in enumerate(row):energy=_add(energy,_mul(h,_mul(state[i+shift],state[j+shift],m),m),m)
            energies.append(energy)
        drift=_add(energies[0],-_mul(parsed['drift_multiplier'],energies[1],m),m);unlinked=_add(drift,-packet,m)
        expected_int={'D':D,'pair_count':len(bank),'nonzero_pairs':nonzero,'weighted_pairs':weighted}
        for key,v in expected_int.items():
            if type(certificate[key]) is not int or certificate[key]!=v:raise AdmissionError('finite '+key+' mismatch')
        expected={'positive_mass':positive,'negative_mass':negative,'weighted_density':weighted_density,'packet':packet,'energy':energies[0],'half_energy':energies[1],'drift':drift,'unlinked':unlinked}
        if any(_rational(certificate[k],k,m)!=v for k,v in expected.items()):raise AdmissionError('finite exact packet/source value mismatch')
        if type(certificate['state']) is not list or len(certificate['state'])!=depth+1 or [_rational(v,'state',m) for v in certificate['state']]!=state:raise AdmissionError('complete original source delay state mismatch')
        out.update(status='VERIFIED_FINITE_PACKET',u=u,**expected_int,**{k:str(v) for k,v in expected.items()},state=[str(v) for v in state],arithmetic_source_admitted=True,complete_ratio_bank_admitted=True,exact_density_balance_verified=True,source_delay_identity_verified=True,unlinked_remainder_unpaid=True,uniform_signed_packet_bound_proved=False,finite_compilation_does_not_prove_all_scale_algorithm=True,weighted_pairs_scope='count of retained nonzero ratio labels, not sumweights or physical edge mass')
    except (ValueError,TypeError,KeyError,OverflowError) as e:return _done(out,m,e)
    return _done(out,m)
