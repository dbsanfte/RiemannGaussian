#!/usr/bin/env python3
"""Taylor centre compression, scalar binomial signal and lookup-table limits.

Optional research replay; not part of Lean builds or ordinary CI.
Run from formal/ with ../.venv/bin/python -B scripts/probe_semiprime_centre_compression.py.
Generated factor labels are used only to verify returned factors.
"""

import math, json, random
import mpmath as mp
from sympy import nextprime
def iroot3(n):
    r=round(n**(1/3))
    while (r+1)**3<=n:r+=1
    while r**3>n:r-=1
    return r
def ceilroot(n):
    s=math.isqrt(n)
    return s+(s*s!=n)


def replay():
    mp.mp.dps = 70
    rng = random.Random(600193)
    rows=[]
    for bits in [30,36,42,48]:
        p=int(nextprime((1<<(bits//2-1))+rng.randrange(1<<(bits//2-2))))
        q=int(nextprime(p+rng.randrange(1,p)))
        N=p*q;r=iroot3(N)
        for d in [3,4]:
            length=max(4,round(2*(r**(.4 if d==3 else .5))))
            mismatches=0; blocks=0; max_error=mp.mpf(0)
            carry_nonzero=0; carry_tests=0
            for start in range(r,2*r,length):
                blocks+=1
                c0=2*mp.sqrt(mp.mpf(N)*start)
                coeff=[c0*mp.binomial(mp.mpf('0.5'),i)/(mp.mpf(start)**i) for i in range(d+1)]
                fc=[float(c) for c in coeff]
                approx=[]
                for off in range(min(length,2*r-start)):
                    val=fc[-1]
                    for c in reversed(fc[:-1]): val=val*off+c
                    # Check rounding using high precision whenever float could matter.
                    if abs(val-round(val))<max(1e-7,abs(val)*3e-15):
                        exact=sum(coeff[i]*mp.mpf(off)**i for i in range(d+1))
                        pred=int(mp.ceil(exact))
                    else: pred=math.ceil(val)
                    true=ceilroot(4*N*(start+off))
                    mismatches+=(pred!=true)
                    approx.append(pred)
                # Rounding destroys the formal degree-(d+1) zero difference.
                ds=approx
                for order in range(d+1):
                    ds=[b-a for a,b in zip(ds,ds[1:])]
                carry_nonzero+=sum(x!=0 for x in ds);carry_tests+=len(ds)
                end=min(length-1,2*r-start-1)
                err=abs(sum(coeff[i]*mp.mpf(end)**i for i in range(d+1))
                        -2*mp.sqrt(mp.mpf(N)*(start+end)))
                max_error=max(max_error,err)
            rows.append({"bits":N.bit_length(),"r":r,"degree":d,"length":length,
              "blocks":blocks,"centre_corrections":mismatches,
              "blocks_plus_corrections":blocks+mismatches,
              "old_literal_centres":r,"max_real_taylor_error":float(max_error),
              "nonzero_next_difference_fraction":carry_nonzero/max(1,carry_tests)})
    print(json.dumps({"centred_polynomial_probe":rows}))
    # Scalar sparse-signal extraction and exact finite-value degeneration.
    P=[11,17,31,101]
    Q=[13,19,53,173]
    scalar=[]
    for p,q in zip(P,Q):
        N=p*q;m=math.isqrt(2*N)
        B=math.comb(N-1,m)%N
        S=(1-((-1)**m)*B)%N
        assert S==p+q
        vals=[]
        for x in [0,1,2,7,19]:
            v=(1+q*pow(x,p,N)+p*pow(x,q,N))%N
            assert v==(1+(p+q)*x)%N
            vals.append(v)
        scalar.append({"N":N,"m":m,"binomial_residue":B,
          "factor_sum_from_residue":S,"true_factor_sum":p+q,"values":vals})
    print(json.dumps({"binomial_factor_sum":scalar}))
    # Powers-of-two lookup saturation: a fully specified bad residue class.
    traces=[]
    for t in [4,6,8,10,12,14,16]:
        W=1<<t;n=W-1
        values={(a+n*pow(a,-1,W))%W for a in range(1,W,2)}
        assert len(values)==W//8
        assert all(s%8==0 for s in values)
        traces.append({"t":t,"W":W,"N_residue":n,"possible_factor_sum_residues":len(values),
          "density":len(values)/W})
    print(json.dumps({"two_adic_lookup_saturation":traces}))


if __name__ == '__main__':
    replay()
