#!/usr/bin/env python3
"""Exact truncated Frobenius signal and reusable residue-mask audit.

Optional research replay; not part of Lean builds or ordinary CI.
Run from formal/ with ../.venv/bin/python -B scripts/probe_semiprime_sparse_signal.py.
Generated factor labels are used only to verify returned factors.
"""

import math, json, random, time
from sympy import primerange
def conv(a,b,N,M):
    out=[0]*min(M,len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b[:M-i]):
                if y: out[i+j]=(out[i+j]+x*y)%N
    while len(out)>1 and out[-1]==0: out.pop()
    return out
def truncpow(N,M):
    a=[1,1]; r=[1]; k=N; hist=[]; mults=0
    while k:
        if k&1:
            r=conv(r,a,N,M); mults+=1
            hist.append(("multiply",len(r),sum(c!=0 for c in r)))
        k>>=1
        if k:
            a=conv(a,a,N,M); mults+=1
            hist.append(("square",len(a),sum(c!=0 for c in a)))
    return r,hist,mults


def replay():
    examples=[]
    checks=0; max_peak_fraction=0
    P=list(primerange(3,200))
    for i,p in enumerate(P):
        for q in P[i+1:]:
            if q>2*p: break
            N=p*q; M=math.isqrt(2*N)+1
            v,h,ops=truncpow(N,M)
            expected=[k for k in range(M) if k in (0,p,q)]
            support=[k for k,x in enumerate(v) if x]
            assert support==expected,(N,support,expected)
            assert [v[k] for k in support] == [1, q, p]
            m = M - 1
            assert (1 - (-1)**m * math.comb(N - 1, m)) % N == p + q
            assert all(math.gcd(v[k],N) in (p,q) for k in support if k)
            assert all(k*v[k]%N==0 for k in range(1,len(v)))
            checks+=1
            if (p,q) in [(11,13),(17,19),(31,53),(101,173)]:
                examples.append({"N":N,"p":p,"q":q,"cutoff":M,"support":support,
                    "coefficients":[v[k] for k in support],
                    "max_intermediate_nonzero":max(x[2] for x in h),
                    "last_steps":h[-3:],"multiplications":ops,
                    "truncated_at_2":sum(c*pow(2,k,N) for k,c in enumerate(v))%N,
                    "ordinary_blackbox_at_2":(pow(3,N,N))})
            max_peak_fraction=max(max_peak_fraction,max(x[2] for x in h)/M)
    print(json.dumps({"sparse_frobenius_checks":checks,"examples":examples,
                     "maximum_intermediate_density":max_peak_fraction}))
    # Reusable residue tables: exact factor-sum possibilities given only N mod W.
    tables=[]
    for W in [16,64,256,1024,30,210,2310]:
        units=[a for a in range(W) if math.gcd(a,W)==1]
        byN={}
        for a in units:
            for b in units:
                n=a*b%W
                byN.setdefault(n,set()).add((a+b)%W)
        sizes=[len(x) for x in byN.values()]
        tables.append({"modulus":W,"unit_residues":len(units),"table_entries":sum(sizes),
            "minimum_possible_sum_residues":min(sizes),"maximum_possible_sum_residues":max(sizes),
            "mean_possible_sum_residues":sum(sizes)/len(sizes),
            "best_fraction":min(sizes)/W,"worst_fraction":max(sizes)/W})
    print(json.dumps({"residue_tables":tables}))


if __name__ == '__main__':
    replay()
