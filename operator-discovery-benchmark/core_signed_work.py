"""Detector language for complete signed prime-log work and causal recovery.

The all-scale signed shell or its recurrence is a generated conjecture.
Exact identities, a paid history kernel, and finite data do not prove it.
"""
from fractions import Fraction as Q
from itertools import product
import gzip
import json
from pathlib import Path
from flint import arb,ctx
import core_bound_synthesis as OLD
import core_pole_growth_obstruction as POLE
import joint_preconditioned_source as LOCAL
import prime_bank_candidates as S

MODES=('nu0','nu1','nu2','mu')
ETA=('0','-1','-1/2','1/3','1/2','2/3','1','3/2','2')
RHOS=('1/2','1')
LOG_POWERS=(0,1,2,3,4)
CUTOFF=1024
MAX_H=524287
TERM_NAMES={'B':'nu0','U':'nu1','power':'nu2','V':'mu'}


def real(x):
    q=Q(x);return arb(q.numerator)/q.denominator


def catalogue(meter):
    result=[]
    for f,eta in product([f for f in OLD.filters() if f['kind']=='delay'],ETA):
        p=dict(target_filter=f,eta=eta,cutoff=CUTOFF)
        result.append(dict(id=len(result),program=p,lane='eta_'+eta,
                           complexity=1+int(bool(f['sign']))+int(eta!='0'),
                           whole_signed_bound_proved=False,RH_proved=False))
        meter.charge(20)
    return result


def recovery_certificate(program):
    eta=Q(program['eta']);f=program['target_filter']
    if program['cutoff']!=CUTOFF or abs(eta)>2 or f['kind']!='delay':
        raise ValueError('declared signed shell domain')
    inv=OLD.recovery(dict(target_filter=f,auxiliary=None))
    return dict(rule='signed_shell_volterra_history',program=program,
        work='integral_X^(2X) ((1-eta)*G(x)^2+eta*G(x)*B_G(x)/log(x))/x^2 dx',
        exact_filtered_log_bank='B_G(x)=B_F(x)-a*B_F(x/2)-a*log(2)*F(x/2)',
        domain='every dyadic X>=1024; full unit-cell integrals; zero prefixes below1',
        eta_absolute_ceiling='2',log2_lower='69/100',local_volterra_upper='3/5',
        history_geometric_sum_square_upper='6',gap_lower='4/5',history_mass_upper='2/5',
        history='N_G(X)<=2W_eta(X)/g_eta(X)+eta^2*(1+sqrt2)/(2*g_eta(X)^2*log(X)^2)*sum_(k=1)^log2X 2^(-k/2)*N_G(X/2^k)',
        gap='g_eta(X)=1-|eta|*(2-sqrt2)/log(X)',
        assumption='W_eta(X)<=K*(1+log2X)^p for every dyadic X>=1024; K>=0,p>=0',
        head='H0=max_(dyadic Y<1024) E_G(Y), all finite units and delayed heads retained',
        conclusion='E_G(X)<=4*max(H0,5K)*(1+log2X)^p for all dyadic X>=1',
        strict_smaller_scale_dependencies=True,filtered_energy_log_loss=0,
        target_recovery=inv,all_scale_work_bound_proved=False,
        whole_signed_bound_proved=False,RH_proved=False)


def admission(program,rho,k,witness,constant=None):
    cert=recovery_certificate(program)
    # The growth theorem is applied AFTER the independently proved work->energy
    # recovery, not by pretending signed work is a nonnegative square.
    proxy=dict(target_filter=program['target_filter'],auxiliary=None)
    pole=POLE.gate(proxy,rho,'0',k,witness)
    if constant is not None and Q(constant)==0:
        pole=POLE.gate(proxy,'1/2','0',0,witness)
        pole=dict(pole,zero_forcing_sharpens_degree=True)
    inverse=cert['target_recovery']
    admitted=inverse['cofinal'] and not pole['uniform_shape_disproved']
    return dict(admitted=admitted,critical_pole_gate=pole,recovery=cert,
        reason='unpaid_inverse_power' if not inverse['cofinal'] else
               'critical_pole_degree_obstruction' if pole['uniform_shape_disproved'] else 'open_signed_work_premise',
        implied_filtered_log_degree=pole['implied_filtered_energy_log_degree'],
        implied_core_log_degree=(pole['implied_filtered_energy_log_degree']+inverse['extra_log_degree']) if inverse['cofinal'] else None,
        whole_signed_bound_proved=False,RH_proved=False)


def prime_log_certificate(source_program):
    if set(t['name'] for t in source_program['terms'])!=set(TERM_NAMES):
        raise ValueError('complete source modes')
    rows=[]
    for term in source_program['terms']:
        row=[]
        for shift,exponent in term['zeta_factors']:
            if Q(exponent).denominator!=1:raise ValueError('integral Euler exponents for this source rule')
            row.append(dict(shift=shift,multiplier=exponent))
        rows.append(dict(mode=TERM_NAMES[term['name']],source_scalar=term['coefficient'],lambda_terms=row))
    return dict(rule='logarithmic_derivation_of_complete_euler_product',rows=rows,
        coefficient_identity='f(n)*log(n)=sum_(d|n,d>=2) Lambda(d)*sum_i c_i*lambda_i(d)*nu_i(n/d)',
        prefix_identity='B_F(x)=sum_(d<=x,d>=2) Lambda(d)*sum_i c_i*lambda_i(d)*A_i(x/d)',
        scope='all actual primes and every positive valuation; exact unit cofactors; no coprimality restriction',
        all_arguments_smaller=True,prime_power_tail_truncated=False,
        supplies_signed_bound=False,whole_signed_bound_proved=False,RH_proved=False)


def source(H,source_program,meter):
    """Complete prime-local source, avoiding unused correction/inverse arrays."""
    if type(H)is not int or not 1<=H<=MAX_H:raise ValueError('complete declared source horizon')
    spf,_,primes=S._sieve(H,meter,18*(H+1)+4096)
    modes={n:[arb(0)]*(H+1) for n in MODES}
    for v in modes.values():v[1]=arb(1)
    local={}
    for p in primes:
        length=1;q=p
        while q<=H:length+=1;q*=p;meter.charge(2)
        root=arb(p).root(6);meter.charge(70)
        local[p]={TERM_NAMES[t['name']]:LOCAL._local_series(t['zeta_factors'],root,length,meter) for t in source_program['terms']}
    exponent=[0]*(H+1);cofactor=[0]*(H+1);cofactor[1]=1
    for n in range(2,H+1):
        p=spf[n];prev=n//p
        if prev%p==0:exponent[n]=exponent[prev]+1;cofactor[n]=cofactor[prev]
        else:exponent[n]=1;cofactor[n]=prev
        for name in MODES:modes[name][n]=modes[name][cofactor[n]]*local[p][name][exponent[n]]
        meter.charge(18)
    beta=arb(9)/2;z=(arb(2)/3).zeta();zv=(arb(4)/3).zeta()
    Ru=beta*(zv/(z*z)-1/z);c=[beta,-beta,-Ru,-beta];meter.charge(1000)
    prefixes={n:[arb(0)]*(H+1) for n in MODES}
    core=[arb(0)]*(H+1);F=[arb(0)]*(H+1);B=[arb(0)]*(H+1)
    for n in range(1,H+1):
        core[n]=sum((q*modes[name][n] for q,name in zip(c,MODES)),arb(0))
        F[n]=F[n-1]+core[n]
        B[n]=B[n-1]+core[n]*arb(n).log()
        for name in MODES:prefixes[name][n]=prefixes[name][n-1]+modes[name][n]
        meter.charge(90)
    meter.live(18*(H+1)+4096)
    return dict(H=H,precision=ctx.prec,modes=modes,prefixes=prefixes,core=core,F=F,log_prefix=B,R_u=Ru,c=c)


def archived_state(directory,H,meter):
    found={}
    with gzip.open(Path(directory)/'producer_vectors.jsonl.gz','rt') as stream:
        for line in stream:
            row=json.loads(line);meter.charge(5*len(row['values']))
            if row['name'] in ('F','log_prefix'):
                if len(row['values'])<=H:raise ValueError('complete archived support')
                found[row['name']]=[arb(v) for v in row['values'][:H+1]]
                meter.charge(8*(H+1))
    if set(found)!={'F','log_prefix'}:raise ValueError('complete signed core and log bank')
    return dict(found,H=H,precision=ctx.prec)


def tables(state,scales,meter):
    """Twelve streaming sufficient moments, no dense pair table or endpoint rule."""
    scales=sorted(set(scales));H=state['H']
    if any(type(X)is not int or X<1 or 2*X-1>H for X in scales):raise ValueError('whole blocks')
    boundaries={0}|{j for X in scales for j in (X-1,2*X-1)}
    sums=[arb(0)]*12;saved={0:list(sums)}
    previous=arb(2).log().expint(1);meter.charge(320)
    for n in range(1,max(boundaries)+1):
        f,h=state['F'][n],state['F'][n//2]
        b,bh=state['log_prefix'][n],state['log_prefix'][n//2]
        if n==1:
            if not b.is_zero() or not bh.is_zero() or not h.is_zero():raise ValueError('complete unit log convention')
            ell=arb(0)
        else:
            following=arb(n+1).log().expint(1);ell=previous-following;previous=following
            meter.charge(320)
            if not ell>0:raise ArithmeticError('strict positive whole-cell integral')
        v=arb(1)/(n*(n+1));base=[f*f,f*h,h*h]
        values=base+[v*t for t in base]+[ell*f*b,ell*f*bh,ell*h*b,ell*h*bh,ell*f*h,ell*h*h]
        for i,t in enumerate(values):sums[i]+=t
        meter.charge(65)
        if n in boundaries:saved[n]=list(sums)
    out={}
    for X in scales:
        row=[a-b for a,b in zip(saved[2*X-1],saved[X-1])]
        row[:3]=[v/(X*X) for v in row[:3]];out[X]=row;meter.charge(30)
    meter.live(2*(H+1)+32*len(boundaries)+4096)
    return out


def measure(program,X,table,meter,cache=None):
    if cache is None:cache={}
    f=program['target_filter'];a=f['sign']*OLD.power(2,f['theta']);eta=real(program['eta'])
    cachekey=(X,f['sign'],f['theta'])
    if cachekey not in cache:
        t=table[X];a2=a*a;log2=arb(2).log()
        E=t[0]-2*a*t[1]+a2*t[2]
        N=t[3]-2*a*t[4]+a2*t[5]
        B=t[6]-a*(t[7]+t[8])+a2*t[9]-a*log2*t[10]+a2*log2*t[11]
        cache[cachekey]=(E,N,B);meter.charge(180)
    E,N,B=cache[cachekey];W=(1-eta)*N+eta*B;meter.charge(8)
    return dict(X=X,energy_filtered=E,critical_energy=N,prime_log_work=B,memory_cross=N-B,work=W,
                dyadic_domain=X>=CUTOFF and X&(X-1)==0,
                all_scale_work_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def weak_reference(program):
    eta=Q(program['eta']);Cg=3*Q(37,2)
    C=4*(abs(1-eta)+abs(eta))*Cg*Cg
    return dict(rule='complete_absolute_shell_reference',program=program,source_residue_ceiling=5,
                source_coefficient_ceiling='37/2',filtered_coefficient_ceiling=str(Cg),
                shell_constant=str(C),step_constant=str(9*C),gamma='1',log_power=2,
                scope='all dyadic X>=1024 and0<=rho<=1; |W(X)|<=shell_constant*X*(1+log2X)^2',
                critical_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)


def recurrence_certificate(program,rho,k,constant,base_bound,head_bound):
    rho,C,B,H=map(Q,(rho,constant,base_bound,head_bound))
    if not 0<=rho<=1 or min(C,B,H)<0 or type(k)is not int or k<0:
        raise ValueError('nonnegative forcing and certified base/head upper bounds')
    if C==0:K=B;p=0
    elif rho<1:K=B+C/(1-rho);p=k
    else:K=B+C;p=k+1
    return dict(rule='signed_upper_dyadic_recurrence',program=program,rho=str(rho),log_power=k,
        constant=str(C),base_scale=CUTOFF,base_upper=str(B),head_energy_upper=str(H),
        base_requirement='W(1024)<=base_upper; all dyadic E_G(Y)<=head_energy_upper for1<=Y<1024',
        premise='W(2X)<=rho*W(X)+constant*(1+log2X)^log_power for every dyadic X>=1024',
        work_upper_constant=str(K),filtered_log_degree=p,filtered_energy_constant=str(4*max(H,5*K)),
        conclusion='E_G(X)<=filtered_energy_constant*(1+log2X)^filtered_log_degree for every dyadic X>=1',
        recovery=recovery_certificate(program),uniform_step_proved=False,
        whole_signed_bound_proved=False,RH_proved=False)


def obligation(record):
    p=record['program'];a=record['admission']
    return dict(id='signed_work_'+str(record['program_id'])+'_'+record['rho']+'_'+str(record['log_power']),
        status='open' if record['status']=='finite_survivor_open_uniform_premise' else record['status'],
        program=p,expression=['subtract',['signed_shell_work',p,'2X'],['multiply',record['rho'],['signed_shell_work',p,'X']]],
        required_bound=dict(constant=record.get('constant'),log_power=record['log_power'],power='0'),
        domain='every dyadic X>=1024; fixed constant; complete signed prime-power bank and exact interval weights',
        proof_chain=['all-prime logarithmic identity: exact','signed shell history recovery: strict smaller-scale contraction',
                     'uniform signed work recurrence: OPEN','conditional upper recurrence induction','paid delay inverse and original recovery'],
        conditional_filtered_log_degree=a['implied_filtered_log_degree'],conditional_core_log_degree=a['implied_core_log_degree'],
        equivalent_growth_presentation=True,recurrence_is_stronger_sufficient_lemma=True,
        coefficients_and_primes_not_replaced_by_random_model=True,
        whole_signed_bound_proved=False,RH_proved=False)
