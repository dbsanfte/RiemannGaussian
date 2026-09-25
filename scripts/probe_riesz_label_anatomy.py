#!/usr/bin/env python3
"""Optional anatomy of literal prime-product examples; no density/bound claim.

This audit distinguishes the moment index N from the summed integer n. It
also records the log-lattice bias of the sparse Mersenne identity regression.
New examples use exact Proth modular certificates and prescribed log shares;
they are deliberately selected examples, not a representative prime sample.
Transcendental values and factorial probabilities are numerical only.
"""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

from probe_riesz_joint_masked import rectangle_values
from probe_riesz_least_order_boundary import lucas_lehmer


def riesz(logs, length):
    return mp.fsum((-1)**sum(bits)*max(mp.mpf(0),length-mp.fsum(
        x*b for x,b in zip(logs,bits))) for bits in itertools.product((0,1),repeat=len(logs)))


def length(n):
    return 2*mp.log(20000**n//(10001**n*(n+1))+2)


def middle_subset_profile(logs,L):
    """Numerical signed divisor staircase after largest/least deletion.

    With n=P*r*b, D=L-log(P), h=log(r), the reduced hinge is
    integral_(D-h)^D sum_(d|b, log(d)<=t) mu(d) dt.  Keep all signs;
    the unit divisor is included. This is a finite identity regression,
    not an interval-certified density or prime-sum estimate.
    """
    T=mp.fsum(logs);D=L-logs[0];h=logs[-1];middle=logs[1:-1]
    terms=[]
    for bits in itertools.product((0,1),repeat=len(middle)):
        x=mp.fsum(v for v,bit in zip(middle,bits) if bit)
        terms.append((x,(-1)**sum(bits),[i+1 for i,bit in enumerate(bits) if bit]))
    cuts=sorted(set([D-h,D]+[x for x,_,_ in terms if D-h<x<D]))
    integral=mp.mpf(0);segments=[]
    for left,right in zip(cuts,cuts[1:]):
        balance=sum(sign for x,sign,_ in terms if x<=(left+right)/2)
        integral+=balance*(right-left)
        segments.append(dict(left_share=mp.nstr(left/T,30),right_share=mp.nstr(right/T,30),
                             even_minus_odd=balance))
    clipped=mp.fsum(sign*min(h,max(mp.mpf(0),D-x)) for x,sign,_ in terms)
    assert abs(integral-clipped)<mp.mpf('1e-100')
    assert abs(integral-riesz(logs[1:],D))<mp.mpf('1e-100')
    return dict(cutoff_share=mp.nstr(D/T,30),least_share=mp.nstr(h/T,30),
                full_weight_balance=sum(sign for x,sign,_ in terms if x<=D-h),
                crossing_subsets=[dict(middle_prime_indices=indices,mu=sign,
                                      log_share=mp.nstr(x/T,30))
                                  for x,sign,indices in sorted(terms) if D-h<x<D],
                signed_staircase=segments,integral_per_log_n=mp.nstr(integral/T,30),
                identity_error=float(abs(integral-clipped)))


def proth_near_log(target):
    """Find p=k*2^m+1, k odd <2^m, a^((p-1)/2)=-1 mod p.

    The check is sufficient, without probabilistic primality: for any prime
    divisor q, a^k has order 2^m modulo q. Thus q>=2^m+1>sqrt(p), excluding
    a composite p. All returned certificates are checked again separately.
    """
    m=int(mp.ceil(target/(2*mp.log(2))))
    two=2**m
    k=max(1,int(mp.ceil(mp.exp(target)/two)))
    if k%2==0:k+=1
    small=[3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97]
    while k<two:
        p=k*two+1
        if all(p%q for q in small):
            for a in [2,3,5,7,11,13,17,19,23,29,31]:
                if pow(a,(p-1)//2,p)==p-1:
                    return p,dict(k=str(k),m=m,witness=a)
                if pow(a,p-1,p)!=1:break
        k+=2
    raise RuntimeError('Certificate search exhausted its Proth interval')


def check_certificate(p,c):
    k=int(c['k']);m=c['m'];a=c['witness']
    assert k>0 and k%2==1 and k<2**m and p==k*2**m+1
    assert pow(a,(p-1)//2,p)==p-1


def describe(N,primes,y=60,certificates=None,exponents=None):
    assert len(set(primes))==len(primes)
    primes=sorted(primes,reverse=True)
    logs=list(map(mp.log,primes));T=mp.fsum(logs);L=length(N)
    n=math.prod(primes);k=len(primes);shares=[x/T for x in logs]
    R=riesz(logs,L);coefficient=-T*R/L;phase=mp.exp(-1j*y*T)
    reflected=[i for i,x in enumerate(logs) if x>=T-L]
    physical=20000**N//(10001**N*(N+1))+2
    masks=dict(squarefree=True,prime_count=3<=k<=55,
               core_window=mp.mpf('1.95')*N<T<=mp.mpf('2.03')*N,
               physical=all(N*N<p<physical*physical for p in primes),
               owner_interior=mp.mpf('.5')<shares[0]<mp.mpf('.6'),
               least_interior=mp.mpf('.005')<shares[-1]<mp.mpf('.06'),
               nondominant=shares[0]<mp.mpf('.65'))
    assert all(masks.values()),masks
    rectangle=float(rectangle_values(N,np.array([float(shares[0])]),np.array([float(shares[-1])]))[0])
    reduced=riesz(logs[1:],L-logs[0])
    # The largest share is >1/2; the reflected cutoff is below that prime.
    assert abs(R+reduced)<mp.mpf('1e-100')
    out=dict(N=N,integer=str(n),decimal_digits=len(str(n)),factor_count=k,moebius=(-1)**k,
             divisor_count=2**k,primes=[str(p) for p in primes],prime_digits=[len(str(p)) for p in primes],
             log_shares=[float(x) for x in shares],total_log=float(T),lambda_ratio=float(L/T),
             riesz_response=float(R),coefficient_per_log_n=float(coefficient/T),
             reflected_large_indices=reflected,rectangle_weight=rectangle,
             phase_height=y,phase=[float(phase.real),float(phase.imag)],
             real_coefficient_phase_per_log_n=float((coefficient/T*phase).real),
             masks=masks,largest_deletion_error=float(abs(R+reduced)),
             cofactor_digit_count=len(str(n//primes[0])),
             middle_subset_profile=middle_subset_profile(logs,L))
    if certificates is not None:
        out['prime_certificates']=[certificates[p] for p in primes]
    if exponents is not None:
        out['mersenne_exponents']=sorted(exponents,reverse=True)
        E=sum(exponents);error=T-E*mp.log(2)
        out['log_lattice_error']=float(error)
        out['phase_angle_error_vs_power_of_two']=float(abs(y*error))
    return out


def mersenne_examples():
    N=328;exponents=[17,19,31,61,89,107,127,521]
    assert all(all(e%d for d in range(2,math.isqrt(e)+1)) for e in exponents)
    assert all(lucas_lehmer(e) for e in exponents)
    primes=[2**e-1 for e in exponents];rows=[]
    for flags in itertools.product((0,1),repeat=len(primes)):
        es=[e for e,b in zip(exponents,flags) if b]
        if len(es)<3:continue
        ps=[2**e-1 for e in es];xs=list(map(mp.log,ps));T=mp.fsum(xs)
        if not mp.mpf('1.95')*N<T<=mp.mpf('2.03')*N:continue
        if not mp.mpf('.5')<max(xs)/T<mp.mpf('.6'):continue
        if not mp.mpf('.005')<min(xs)/T<mp.mpf('.06'):continue
        rows.append(describe(N,ps,exponents=es))
    assert len(rows)==5
    return rows


def index_ranges():
    rows=[]
    for power in [16,17,18,19]:
        N=2**power;low=mp.mpf('1.95')*N;high=mp.mpf('2.03')*N
        rows.append(dict(N=N,factorization=f'2^{power}',
            possible_label_digits=[int(mp.floor(low/mp.log(10)))+1,int(mp.floor(high/mp.log(10)))+1],
            j_interval=[(21*N+39)//40,23*N//40],
            h_plus_one_interval=[(N+99)//100,N//25],N_mod_100=N%100,
            lambda_interval=[float(length(N)/high),float(length(N)/low)]))
    return rows


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args();mp.mp.dps=600;N=512
    shapes=[['.55','.43','.02'],['.55','.26','.17','.02'],
            ['.55','.20','.12','.11','.02'],['.55','.17','.12','.08','.06','.02'],
            ['.55','.13','.105','.08','.065','.05','.02']]
    cache={};certificates={};rows=[]
    for shape in shapes:
        ps=[]
        for share in shape:
            if share not in cache:
                p,c=proth_near_log(mp.mpf(2*N)*mp.mpf(share));check_certificate(p,c)
                cache[share]=p;certificates[p]=c
            ps.append(cache[share])
        row=describe(N,ps,certificates=certificates)
        row['target_log_shares']=shape
        row['total_log_error_from_target']=float(mp.log(int(row['integer']))-2*N)
        rows.append(row)
    report=dict(scope='Chosen certified-prime examples and order-index anatomy, NOT a statistical sample or a cancellation estimate.',
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        numerical_precision=mp.mp.dps,indices=index_ranges(),mersenne_regression=mersenne_examples(),
        constructed_examples=rows,
        prime_certificate_argument='p=k*2^m+1, k odd <2^m, a^((p-1)/2)=-1 mod p. For each prime q|p, a^k has exact order 2^m modulo q; hence q>=2^m+1>sqrt(p). This is an exact integer certificate, not a new Lean theorem.',
        limitations=['No exhaustive enumeration of the actual core band.',
                    'No representative distribution, density, or count-dominance assertion.',
                    'The constructed primes also have a deliberate Proth shape.',
                    'No Riesz-sign rule follows from prime-count parity alone.',
                    'No arithmetic floor, zero exclusion, or bound is proved.'])
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'indices':report['indices'],'mersenne':[{k:r[k] for k in ['mersenne_exponents','decimal_digits','log_shares','coefficient_per_log_n','phase','phase_angle_error_vs_power_of_two']} for r in report['mersenne_regression']],
                     'constructed':[{k:r[k] for k in ['factor_count','prime_digits','log_shares','coefficient_per_log_n','phase','rectangle_weight','total_log_error_from_target']} for r in rows]},indent=2))


if __name__=='__main__':main()
