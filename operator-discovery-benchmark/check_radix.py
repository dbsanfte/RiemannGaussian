#!/usr/bin/env python3
"""Independent digitwise kernels, Omega recurrences and radix log degree."""

from fractions import Fraction as Q
from math import factorial,comb
from pathlib import Path
import json
import time

from check_gap import factors,divisors,omega,exp_D,log_D,D

BASE=Path(__file__).resolve().parent
DEST=BASE/'radix-results'


def allowed(i,j,b):
    while i or j:
        if i%b+j%b>=b:return False
        i//=b;j//=b
    return True


def E(h,b):
    out=[Q(0)]*len(h);out[1]=Q(1)
    for n in range(2,len(h)):
        out[n]=sum((omega(d)*h[d]*out[n//d] for d in divisors(n) if d>1 and allowed(omega(d),omega(n//d),b)),Q(0))/omega(n)
    return out


def L(f,b):
    out=[Q(0)]*len(f)
    for n in range(2,len(f)):
        out[n]=f[n]-sum((omega(d)*out[d]*f[n//d] for d in divisors(n) if 1<d<n and allowed(omega(d),omega(n//d),b)),Q(0))/omega(n)
    return out


def G(a,c,b):
    return [Q(0)]+[sum((a[d]*c[n//d] for d in divisors(n) if allowed(omega(d),omega(n//d),b)),Q(0)) for n in range(1,len(a))]


def graded_product(a,c,b):
    return [sum((a[i]*c[n-i] for i in range(n+1) if allowed(i,n-i,b)),Q(0)) for n in range(len(a))]


def graded_exp(h,b):
    term=[Q(1)]+[Q(0)]*(len(h)-1);out=list(term)
    for k in range(1,len(h)):
        term=[v/k for v in graded_product(term,h,b)]
        if not any(term):break
        out=[v+w for v,w in zip(out,term)]
    return out


def audit(source):
    generic=source['generic_transfer_laws']
    for row in generic['records']:
        b=row['radix'];f=list(map(Q,row['input']));g=list(map(Q,row['second_input']))
        S=E(log_D(f),b);assert S==list(map(Q,row['output']))
        assert exp_D(L(S,b))==f and E(log_D(exp_D(L(f,b))),b)==f
        assert E(log_D(D(f,g)),b)==G(S,E(log_D(g),b),b)
        R=E([v/2 for v in log_D(f)],b)
        assert G(R,R,b)==S and R!=exp_D([v/2 for v in log_D(S)])
        # Exact kernel associativity on fresh degrees is supplementary to
        # the written digitwise three-way proof, not a universal certificate.
        for i in range(19):
            for j in range(19):
                for k in range(19):
                    assert allowed(i,j,b)*allowed(i+j,k,b)==allowed(j,k,b)*allowed(i,j+k,b)
    count=0
    for row in source['zeta_profiles']['records']:
        b,beta,N=row['radix'],Q(row['beta']),row['encoded_cutoff']
        h=[Q(0)]*(N+1)
        for n in range(2,N+1):
            fs=factors(n)
            if len(fs)==1:h[n]=beta/next(iter(fs.values()))
        actual=E(h,b);ordinary=exp_D(h)
        assert actual==list(map(Q,row['coefficients']))
        assert all(0<=a<=c for a,c in zip(actual,ordinary));count+=N-1
    for row in source['log_polynomial_grammar']['records']:
        b=row['radix'];higher=list(map(Q,row['higher_log_coefficients']))
        values=[]
        for z in range(9):
            h=list(higher);h[1]=Q(z);values.append(sum(graded_exp(h,b),Q(0)))
        assert values==list(map(Q,row['observations']))
        deltas=[];level=values
        while level:
            deltas.append(level[0]);level=[v-u for u,v in zip(level,level[1:])]
        degree=max(j for j,v in enumerate(deltas) if v)
        assert degree==row['inferred_polynomial_degree']==b-1
        coarsened=[higher[b*j] for j in range((row['grade_cutoff']-b+1)//b+1)]
        leading=sum(graded_exp(coarsened,b),Q(0))/factorial(b-1)
        assert leading==Q(row['inferred_leading_coefficient'])==deltas[b-1]/factorial(b-1)
    control=source['zeta_profiles']['ordinary_root_type_control']
    assert Q(control['transfer_of_ordinary_input_half_root'])==Q(1,6)
    assert Q(control['ordinary_output_half_root'])==Q(-1,48)
    wrong=source['composite_radix_binomial_filter_negative_control']
    assert int(comb(2,1)%4!=0)*int(comb(4,2)%4!=0)==wrong['binomial_nondivisibility_left']==1
    assert int(comb(3,1)%4!=0)*int(comb(4,1)%4!=0)==wrong['binomial_nondivisibility_right']==0
    assert wrong['actual_radix_digit_kernel_parenthesizations']==[0,0]
    return count


def main():
    start=time.monotonic();source=json.loads((DEST/'radix_search.json').read_text());assert source['all_passed']
    count=audit(source)
    checks={'independent_digitwise_associativity_and_generic_inverse':True,
            'independent_Omega_EXP_zeta_profiles':True,
            'independent_graded_powers_and_self_similar_leading_coefficient':True,
            'ordinary_versus_typed_roots_distinguished':source['ordinary_output_root_fidelity']=='rejected',
            'historical_novelty_and_RH_claims_withheld':not source['historical_novelty_established'] and not source['new_RH_estimate_proved']}
    out={'checks':checks,'encoded_zeta_indices_checked':count,'production_imports':False,
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'radix_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent global radix exact audit:',sum(checks.values()),'/',len(checks),'indices',count,'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':main()
