#!/usr/bin/env python3
"""Single-input extraction probes with every sieve/projection cost charged.

The order-projection pass has a one-sixth-sized work budget and an explicit
coverage condition, not a generic one-sixth factorisation guarantee.
No factor labels or independent square-root-sized table enter recovery.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import statistics
import sys
import time
import gmpy2

WEIGHTED = runpy.run_path(str(Path(__file__).with_name("probe_semiprime_weighted_batch.py")))
tree, chirp, descend = (WEIGHTED[k] for k in ("tree", "chirp", "descend"))

def ceil_root(n, degree):
    r = int(gmpy2.iroot(n, degree)[0])
    return r + (r**degree < n)

def primes_upto(bound):
    sieve = bytearray(b"\x01") * (bound + 1)
    if bound >= 1:
        sieve[:2] = b"\x00\x00"
    for p in range(2, math.isqrt(bound) + 1):
        if sieve[p]:
            start = p*p
            sieve[start:bound+1:p] = b"\x00" * ((bound-start)//p+1)
    return [p for p in range(2, bound+1) if sieve[p]]

def projection_powers(bound, pmax):
    """All prime powers needed to remove <=bound primes from an order <=pmax."""
    powers = []
    for prime in primes_upto(bound):
        power = prime
        while power*prime <= pmax:
            power *= prime
        powers.append((prime, power))
    return powers

def projected_order_test(n, alpha, limit):
    """Exact geometric polynomial certificate; examines the first nonunit block."""
    divisor = math.gcd(alpha, n)
    if 1 < divisor < n:
        return {"status": "factor", "factor": divisor, "work": 0}
    if divisor != 1:
        return {"status": "nonunit", "factor": None, "work": 0}
    width = ceil_root(limit, 2)
    blocks = (limit + width - 1)//width
    values, v = [], 1
    for _ in range(width):
        values.append(v)
        v = v*alpha % n
    node = tree(values, n)
    outputs = chirp(node[0], v, v, blocks, n)
    for index, value in enumerate(outputs):
        g = math.gcd(value, n)
        if 1 < g < n:
            return {"status": "factor", "factor": g, "work": width+blocks}
        if g == n:
            point = pow(v, index+1, n)
            factor = descend(node, point, n)
            return {"status": "factor" if factor else "shared-order",
                    "factor": factor, "work": width+blocks,
                    "first_block_end": (index+1)*width}
    return {"status": "certified-large-order", "factor": None,
            "work": width+blocks, "certified_through": width*blocks}

def factor_projected_unseparated(n, base=2):
    """Factor or certified failure at explicitly bounded one-sixth work.

    Public input: n and base. Smaller prime, if present, is at most sqrt(n).
    Fully removes small prime powers from that prime's base order.
    """
    if n < 4:
        raise ValueError("composite input >=4 required")
    if n % 2 == 0:
        return {"status": "factor", "factor": 2, "bound": 0}
    root = math.isqrt(n)
    if root*root == n:
        return {"status": "factor", "factor": root, "bound": 0}
    g = math.gcd(base, n)
    if 1 < g < n:
        return {"status": "factor", "factor": g, "bound": 0}
    if g != 1:
        return {"status": "nonunit-base", "factor": None, "bound": 0}
    bound = ceil_root(n, 6)
    powers = projection_powers(bound, root)
    alpha = base % n
    for _, power in powers:
        alpha = int(gmpy2.powmod(alpha, power, n))
    g = math.gcd(alpha-1, n)
    info = {"bound": bound, "order_limit": bound*bound,
            "projection_count": len(powers),
            "projection_exponent_bits": sum(power.bit_length() for _, power in powers)}
    if 1 < g < n:
        return {**info, "status": "factor", "factor": g, "stage": "smooth"}
    if g == n:
        # Replay the known prime-power projection only on a shared collapse.
        alpha = base % n
        for prime, power in powers:
            while power > 1:
                alpha = int(gmpy2.powmod(alpha, prime, n))
                g = math.gcd(alpha-1, n)
                if 1 < g < n:
                    return {**info, "status": "factor", "factor": g,
                            "stage": "projection-unwind"}
                if g == n:
                    return {**info, "status": "shared-projection", "factor": None}
                power //= prime
        return {**info, "status": "shared-projection", "factor": None}
    result = projected_order_test(n, alpha, bound*bound)
    return {**info, **result, "stage": "geometric",
            "projected_base": alpha}

def factor_projected(n, base=2, order_divisor=16, max_bases=32):
    """Exact N-1 separation, charged smooth projection, then short order cover.

    For squarefree pq, the two separated local orders are coprime.
    A bounded witness search can still report kernel-unresolved; there is
    no assumption that a fixed small base is a nontrivial witness.
    """
    if n < 4 or order_divisor < 1 or max_bases < 1:
        raise ValueError("positive budget and composite n>=4 required")
    if n % 2 == 0:
        return {"status":"factor", "factor":2, "stage":"even", "bound":0}
    root = math.isqrt(n)
    if root*root == n:
        return {"status":"factor", "factor":root, "stage":"square", "bound":0}
    bound = ceil_root(n, 6)
    for index in range(max_bases):
        witness = base + index
        g = math.gcd(witness, n)
        if 1 < g < n:
            return {"status":"factor", "factor":g, "stage":"base-gcd", "bound":bound}
        if g != 1:
            continue
        alpha = int(gmpy2.powmod(witness, n-1, n))
        if alpha != 1:
            break
    else:
        return {"status":"kernel-unresolved", "factor":None, "bound":bound}
    info = {"bound":bound, "order_limit":max(1,bound*bound//order_divisor),
            "order_divisor":order_divisor, "base":witness, "base_count":index+1}
    g = math.gcd(alpha-1,n)
    if 1 < g < n:
        return {**info,"status":"factor","factor":g,"stage":"separator"}
    powers = projection_powers(bound,root)
    for index, (_,power) in enumerate(powers):
        alpha = int(gmpy2.powmod(alpha,power,n))
        g = math.gcd(alpha-1,n)
        if 1 < g < n:
            return {**info,"status":"factor","factor":g,"stage":"smooth",
                    "projection_count":index+1}
        if g == n:
            return {**info,"status":"shared-projection","factor":None}
    result = projected_order_test(n,alpha,info["order_limit"])
    return {**info,**result,"stage":"geometric","projected_base":alpha,
            "projection_count":len(powers),
            "projection_exponent_bits":sum(power.bit_length() for _,power in powers)}

def factor_hybrid(n, order_divisor=16):
    """Single-input prepass followed by the existing balanced weighted search.

    The prepass's work scale does not change the fallback exponent.
    A fixed-base fallback failure is reported explicitly.
    """
    pre = factor_projected(n, order_divisor=order_divisor)
    if pre["factor"]:
        return {**pre,"path":"projection"}
    factor, _, reason = WEIGHTED["factor_batched"](n,"hybrid")
    return {"status":"factor" if factor else "weighted-failure", "factor":factor,
            "path":"weighted", "reason":reason,"projection_status":pre["status"]}

def lucas_pair(t, order, modulus):
    """V_order(t), V_(order+1)(t), V_0=2,V_1=t; exact fast doubling."""
    a, b = 2 % modulus, t % modulus
    for bit in bin(order)[2:]:
        even = (a*a-2) % modulus
        middle = (a*b-t) % modulus
        following = (b*b-2) % modulus
        a, b = (even, middle) if bit == "0" else (middle, following)
    return a, b

def folded_frobenius(n, t):
    """(t+2)^((n-1)/2)-Q_((n-1)/2)(t) without a long polynomial."""
    if n < 3 or n % 2 == 0:
        raise ValueError("odd n>=3 required")
    divisor = math.gcd(t+2, n)
    if 1 < divisor < n:
        return {"factor": divisor, "residue": None}
    if divisor != 1:
        return {"factor": None, "residue": None}
    order = (n-1)//2
    a, b = lucas_pair(t, order, n)
    q = (a+b)*pow(t+2, -1, n) % n
    residue = (pow(t+2, order, n)-q) % n
    g = math.gcd(residue, n)
    return {"factor": g if 1 < g < n else None, "residue": residue}

def validate():
    checks = {"geometric_order": 0, "folded_identity": 0, "local_order_separation":0,
              "nilpotent_prefix": 0, "projection": 0}
    for n in (17*19, 101*103, 101*173, 257*263, 1009*1013):
        for base in (2,3,5,7):
            if math.gcd(base,n) != 1:
                continue
            for limit in (1,2,3,4,5,9,16,25,40,63,100):
                out = projected_order_test(n,base,limit)
                if out["factor"]:
                    f = out["factor"]
                    assert 1 < f < n and n % f == 0
                elif out["status"] == "certified-large-order":
                    assert all(math.gcd(pow(base,i,n)-1,n)==1
                               for i in range(1,out["certified_through"]+1))
                else:
                    assert any(pow(base,i,n)==1 for i in
                               range(1,out["first_block_end"]+1))
                checks["geometric_order"] += 1
    # Exact cross-multiplied Laurent identity; no division by x+1.
    for n in range(3,100,2):
        for x in range(1,min(n,16)):
            if math.gcd(x,n)!=1:
                continue
            t=(x+pow(x,-1,n)) % n
            m=(n-1)//2
            q0,q1=1,1
            for _ in range(m):
                q0,q1=(t*q0-q1) % n,q0
            right=pow(x,m,n)*(x+1)*(pow(t+2,m,n)-q0) % n
            left=(pow(x+1,n,n)-1-pow(x,n,n)) % n
            assert left==right,(n,x)
            if math.gcd(t+2,n)==1:
                assert folded_frobenius(n,t)["residue"]==(pow(t+2,m,n)-q0)%n
            checks["folded_identity"] += 1
    primes=primes_upto(199)
    for i,p in enumerate(primes):
        for q in primes[i:]:
            n=p*q
            if n % 2==0:
                continue
            # Low-degree nilpotent projection: no positive coefficients before p.
            assert all(math.comb(n,k)%n==0 for k in range(1,p))
            checks["nilpotent_prefix"] += 1
            out=factor_projected(n,order_divisor=1)
            if out["factor"]:
                assert out["factor"] in (p,q),(n,out)
            elif out["status"]=="certified-large-order":
                a=out["projected_base"];b=out["bound"]
                assert all(pow(a,d,p)!=1 and pow(a,d,q)!=1
                           for d in range(1,b*b+1))
                # Audit only: compute the actual order using known factors.
                from sympy.ntheory import n_order
                order=int(n_order(a,p))
                assert order > b*b
                from sympy import factorint
                factors=factorint(order)
                assert all(int(prime)>b for prime in factors)
                assert sum(factors.values())<=2
            else:
                assert out["status"]=="kernel-unresolved",(n,out)
            if p!=q:
                from sympy.ntheory import n_order
                for base in (2,3,5,7):
                    if math.gcd(base,n)!=1:continue
                    rp=int(n_order(pow(base,n-1,p),p))
                    rq=int(n_order(pow(base,n-1,q),q))
                    assert math.gcd(rp,rq)==1,(n,base,rp,rq)
                    checks["local_order_separation"]+=1
            checks["projection"] += 1
    return checks

def benchmark(bits_list, cases, seed, order_divisor=16, repeats=3):
    from sympy import factorint
    rng=random.Random(seed)
    schedule_rng=random.Random(seed ^ 0x5A31E)
    records=[]
    for bits in bits_list:
        lo=1<<(bits//2-1);hi=(1<<(bits//2))-100
        corpus=[]
        while len(corpus)<cases:
            p=int(gmpy2.next_prime(rng.randrange(lo,hi)))
            q=int(gmpy2.next_prime(rng.randrange(lo,hi)))
            if p!=q and q<hi+100:
                corpus.append((min(p,q),max(p,q)))
        timings={"projection":[],"weighted":[],"hybrid":[],"folded":[]}
        outcomes={};stages={};rough_counts={};solved=0;folded_solved=0
        inputs=[];examples=[]
        for p,q in corpus:
            n=p*q;inputs.append(str(n))
            def weighted_call():
                f,_,reason=WEIGHTED["factor_batched"](n,"hybrid")
                return {"factor":f,"reason":reason}
            def folded_call():
                f=next((f for t in range(2,15)
                        if (f:=folded_frobenius(n,t)["factor"])),None)
                return {"factor":f}
            methods={"projection":lambda:factor_projected(n,order_divisor=order_divisor),
                     "weighted":weighted_call,
                     "hybrid":lambda:factor_hybrid(n,order_divisor=order_divisor),
                     "folded":folded_call}
            per={name:[] for name in methods};results={}
            for _ in range(repeats):
                names=list(methods);schedule_rng.shuffle(names)
                for name in names:
                    begin=time.perf_counter();out=methods[name]();elapsed=time.perf_counter()-begin
                    if out["factor"]:assert out["factor"] in (p,q),(n,name,out)
                    if name in ("weighted","hybrid"):assert out["factor"] is not None,(n,name,out)
                    results[name]=out;per[name].append(elapsed*1000)
            for name,values in per.items():timings[name].append(statistics.mean(values))
            pre=results["projection"]
            outcomes[pre["status"]]=outcomes.get(pre["status"],0)+1
            stages[pre["stage"]]=stages.get(pre["stage"],0)+1
            if pre["factor"]:
                assert pre["factor"] in (p,q);solved+=1
            b=ceil_root(n,6)
            rough=[(int(r),int(e)) for r,e in factorint(p-1).items() if r>b]
            assert sum(e for _,e in rough)<=2
            typ="smooth" if not rough else ("one-rough" if sum(e for _,e in rough)==1 else "two-rough")
            rough_counts[typ]=rough_counts.get(typ,0)+1
            if not pre["factor"] and len(examples)<4:
                examples.append({"n":str(n),"p":str(p),"q":str(q),
                                 "p_minus_1_rough":rough,"status":pre["status"]})
            fold=results["folded"]["factor"]
            if fold:
                assert fold in (p,q);folded_solved+=1
        records.append({"nominal_bits":bits,"cases":cases,
                        "projection_solved":solved,"folded_solved":folded_solved,
                        "projection_outcomes":outcomes,"projection_stages":stages,
                        "smaller_prime_rough_counts":rough_counts,
                        "median_ms":{k:statistics.median(v) for k,v in timings.items()},
                        "total_ms":{k:sum(v) for k,v in timings.items()},
                        "survivor_examples":examples,
                        "inputs_decimal":inputs})
    return {"seed":seed,"order_divisor":order_divisor,"repeats":repeats,
            "protocol":"Actual full calls, shuffled method order, per-input mean then corpus median; no cross-input cache.",
            "records":records}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=("validate","benchmark","factor","hybrid"))
    parser.add_argument("n",type=int,nargs="?")
    parser.add_argument("--bits",type=int,nargs="+",default=[32,40,48,56,64])
    parser.add_argument("--cases",type=int,default=24)
    parser.add_argument("--seed",type=int,default=2026100217)
    parser.add_argument("--order-divisor",type=int,default=16)
    parser.add_argument("--repeats",type=int,default=3)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    if args.command=="validate":
        result={"checks":validate()}
    elif args.command in ("factor","hybrid"):
        if args.n is None:parser.error("factor needs N")
        result=(factor_projected if args.command=="factor" else factor_hybrid)(
            args.n,order_divisor=args.order_divisor)
    else:
        result=benchmark(args.bits,args.cases,args.seed,args.order_divisor,args.repeats)
    result["python_version"]=sys.version
    result["source_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    encoded=json.dumps(result,indent=2)+"\n"
    if args.output:args.output.write_text(encoded)
    print(encoded,end="")

if __name__=="__main__":
    main()
