#!/usr/bin/env python3
"""Colour-guided quadratic order extraction for one semiprime.

Uses Jacobi colour, not either hidden Legendre colour, to select N+1.
Known group/order and polynomial stage-two techniques are combined with
the exact local-period separator. Coverage remains conditional.
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
import time
import gmpy2

SINGLE = runpy.run_path(str(Path(__file__).with_name("probe_semiprime_single_extraction.py")))
SCALAR = SINGLE["WEIGHTED"]["mul"]

class QuadraticRing:
    def __init__(self,n,discriminant):
        self.n=n; self.d=discriminant % n
    def add(self,a,b):
        return ((a[0]+b[0])%self.n,(a[1]+b[1])%self.n)
    def mul(self,a,b):
        return ((a[0]*b[0]+self.d*a[1]*b[1])%self.n,
                (a[0]*b[1]+a[1]*b[0])%self.n)
    def power(self,a,e):
        out=(1,0)
        while e:
            if e&1:out=self.mul(out,a)
            e//=2
            if e:a=self.mul(a,a)
        return out
    def norm(self,a):
        return (a[0]*a[0]-self.d*a[1]*a[1])%self.n
    def inverse_one(self,a):
        assert self.norm(a)==1
        return (a[0],-a[1]%self.n)
    def poly_mul(self,a,b):
        # Three exact scalar convolutions; the signed cross terms stay coupled.
        xx=SCALAR(a[0],b[0],self.n)
        yy=SCALAR(a[1],b[1],self.n)
        aa=[(x+y)%self.n for x,y in zip(*a)]
        bb=[(x+y)%self.n for x,y in zip(*b)]
        cross=SCALAR(aa,bb,self.n)
        return ([(x+self.d*y)%self.n for x,y in zip(xx,yy)],
                [(z-x-y)%self.n for x,y,z in zip(xx,yy,cross)])

def polynomial_tree(ring,roots):
    nodes=[(([-x%ring.n,1],[-y%ring.n,0]),None,None) for x,y in roots]
    while len(nodes)>1:
        nxt=[]
        for i in range(0,len(nodes),2):
            if i+1==len(nodes):nxt.append(nodes[i]);continue
            left,right=nodes[i:i+2]
            nxt.append((ring.poly_mul(left[0],right[0]),left,right))
        nodes=nxt
    return nodes[0]

def polynomial_value(ring,poly,x):
    out=(0,0)
    for a,b in reversed(list(zip(*poly))):
        out=ring.add(ring.mul(out,x),(a,b))
    return out

def descend(ring,node,point):
    g=math.gcd(ring.norm(polynomial_value(ring,node[0],point)),ring.n)
    if 1<g<ring.n:return g
    if g==ring.n and node[1] is not None:
        return descend(ring,node[1],point) or descend(ring,node[2],point)
    return None

def chirp(ring,poly,start,q,count):
    degree=len(poly[0])-1;seq=[];v=step=(1,0)
    for _ in range(degree+count):
        seq.append(v);v=ring.mul(v,step);step=ring.mul(step,q)
    inverse=ring.inverse_one(q);v=step=s=(1,0);tw=[]
    for coefficient in zip(*poly):
        tw.append(ring.mul(ring.mul(coefficient,v),s))
        v=ring.mul(v,step);step=ring.mul(step,inverse);s=ring.mul(s,start)
    conv=ring.poly_mul(tuple(map(list,zip(*tw[::-1]))),tuple(map(list,zip(*seq))))
    out=[];v=step=(1,0)
    for i in range(count):
        out.append(ring.mul((conv[0][degree+i],conv[1][degree+i]),v))
        v=ring.mul(v,step);step=ring.mul(step,inverse)
    return out

def chirp_real_tilt(ring,poly,beta,width,count):
    """Exact common phase before projection, not a floating-point tilt.

    alpha=beta^2, even width=b, roots alpha^0,...,alpha^(b-1).
    F(alpha^(b*(i+1))) = beta^(b*b*(i+1)+b*(b-1)//2) * real_scalar.
    Thus the chirp convolution has a KNOWN norm-one phase too. Compute
    only its real coordinate with two scalar convolutions, then divide
    out that coordinate. A nonunit phase coordinate itself gives a factor.
    """
    assert width%2==0 and len(poly[0])==width+1
    alpha=ring.power(beta,2);q=ring.power(alpha,width)
    seq=[];v=step=(1,0)
    for _ in range(width+count):
        seq.append(v);v=ring.mul(v,step);step=ring.mul(step,q)
    inverse=ring.inverse_one(q);v=step=s=(1,0);tw=[]
    for coefficient in zip(*poly):
        tw.append(ring.mul(ring.mul(coefficient,v),s))
        v=ring.mul(v,step);step=ring.mul(step,inverse);s=ring.mul(s,q)
    real=SCALAR([a[0] for a in tw[::-1]],[a[0] for a in seq],ring.n)
    imag=SCALAR([a[1] for a in tw[::-1]],[a[1] for a in seq],ring.n)
    coordinates=[];phase=ring.power(beta,width*width+width*(width-1)//2)
    step=ring.power(beta,width*width);increment=ring.power(beta,2*width)
    for i in range(count):
        g=math.gcd(phase[0],ring.n)
        if 1<g<ring.n:return {"factor":g,"values":None,"fallback":False}
        if g!=1:
            # Unneeded for separated local periods, but preserve correctness
            # for arbitrary caller-supplied units too.
            original=chirp(ring,poly,q,q,count)
            return {"factor":None,"values":original,"fallback":True}
        coordinates.append(phase[0])
        phase=ring.mul(phase,step);step=ring.mul(step,increment)
    # One inversion, all input-specific prefixes charged to this query.
    prefixes=[1]
    for coordinate in coordinates:prefixes.append(prefixes[-1]*coordinate%ring.n)
    inv=pow(prefixes[-1],-1,ring.n);inverses=[0]*count
    for i in range(count-1,-1,-1):
        inverses[i]=inv*prefixes[i]%ring.n;inv=inv*coordinates[i]%ring.n
    values=[(real[width+i]+ring.d*imag[width+i])*inverses[i]%ring.n
            for i in range(count)]
    return {"factor":None,"values":values,"fallback":False}

def order_test(ring,alpha,limit):
    width=SINGLE["ceil_root"](limit,2);blocks=(limit+width-1)//width
    roots=[];v=(1,0)
    for _ in range(width):
        roots.append(v);v=ring.mul(v,alpha)
    node=polynomial_tree(ring,roots)
    outputs=chirp(ring,node[0],v,v,blocks)
    for index,value in enumerate(outputs):
        g=math.gcd(ring.norm(value),ring.n)
        if 1<g<ring.n:
            return {"status":"factor","factor":g,"work":width+blocks}
        if g==ring.n:
            factor=descend(ring,node,ring.power(v,index+1))
            return {"status":"factor" if factor else "shared-order",
                    "factor":factor,"work":width+blocks}
    return {"status":"certified-large-order","factor":None,"work":width+blocks,
            "certified_through":width*blocks}

def order_test_tilt(ring,beta,limit):
    g=math.gcd(beta[0]-1,ring.n)
    if 1<g<ring.n:return {"status":"factor","factor":g,"work":0,"tilted":True}
    alpha=ring.power(beta,2)
    g=math.gcd(alpha[0]-1,ring.n)
    if 1<g<ring.n:return {"status":"factor","factor":g,"work":0,"tilted":True}
    width=SINGLE["ceil_root"](limit,2)
    width+=width%2
    blocks=(limit+width-1)//width
    roots=[];v=(1,0)
    for _ in range(width):roots.append(v);v=ring.mul(v,alpha)
    node=polynomial_tree(ring,roots)
    out=chirp_real_tilt(ring,node[0],beta,width,blocks)
    info={"work":width+blocks,"tilted":True,"fallback":out["fallback"]}
    if out["factor"]:return {**info,"status":"factor","factor":out["factor"]}
    for i,value in enumerate(out["values"]):
        scalar=ring.norm(value) if out["fallback"] else value
        g=math.gcd(scalar,ring.n)
        if 1<g<ring.n:return {**info,"status":"factor","factor":g}
        if g==ring.n:
            f=descend(ring,node,ring.power(v,i+1))
            return {**info,"status":"factor" if f else "shared-order","factor":f}
    return {**info,"status":"certified-large-order","factor":None,
            "certified_through":width*blocks}

def factor_quadratic(n,order_divisor=256,tilted=False,discriminant=None):
    if n<4 or order_divisor<1:raise ValueError("positive budget, composite n>=4 required")
    if n%2==0:return {"status":"factor","factor":2,"stage":"even"}
    root=math.isqrt(n)
    if root*root==n:return {"status":"factor","factor":root,"stage":"square"}
    twin=math.isqrt(n+1)
    if twin*twin==n+1:
        return {"status":"factor","factor":twin-1,"stage":"equal-local-cardinalities"}
    if discriminant is None:
        for d in (-1,2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
            g=math.gcd(d,n)
            if 1<g<n:return {"status":"factor","factor":g,"stage":"colour-gcd"}
            if g==1 and gmpy2.jacobi(d,n)==-1:break
        else:return {"status":"colour-unresolved","factor":None}
    else:
        d=discriminant;g=math.gcd(d,n)
        if 1<g<n:return {"status":"factor","factor":g,"stage":"colour-gcd"}
        if g!=1:return {"status":"nonunit-discriminant","factor":None}
    colour=int(gmpy2.jacobi(d,n));exponent=n-colour
    ring=QuadraticRing(n,d)
    for parameter in range(1,33):
        denom=(parameter*parameter-d)%n;g=math.gcd(denom,n)
        if 1<g<n:return {"status":"factor","factor":g,"stage":"parameter-gcd"}
        if g!=1:continue
        inverse=pow(denom,-1,n)
        unit=((parameter*parameter+d)*inverse%n,2*parameter*inverse%n)
        assert ring.norm(unit)==1
        alpha=ring.power(unit,exponent)
        if alpha!=(1,0):break
    else:return {"status":"kernel-unresolved","factor":None}
    bound=SINGLE["ceil_root"](n,6)
    info={"bound":bound,"order_limit":max(1,bound*bound//order_divisor),
          "discriminant":d,"jacobi":colour,"separator_exponent":str(exponent),
          "parameter":parameter,"order_divisor":order_divisor}
    g=math.gcd(alpha[0]-1,n)
    if 1<g<n:return {**info,"status":"factor","factor":g,"stage":"separator"}
    powers=SINGLE["projection_powers"](bound,root+1)
    for index,(_,power) in enumerate(powers):
        alpha=ring.power(alpha,power)
        g=math.gcd(alpha[0]-1,n)
        if 1<g<n:
            return {**info,"status":"factor","factor":g,"stage":"smooth",
                    "projection_count":index+1}
        if g==n:return {**info,"status":"shared-projection","factor":None}
    test=order_test_tilt(ring,alpha,info["order_limit"]) if tilted else order_test(ring,alpha,info["order_limit"])
    return {**info,**test,
            "stage":"geometric","projected_base":alpha,"projection_count":len(powers)}

def factor_hybrid_colour(n,minus_divisor=16,plus_divisor=256):
    out=SINGLE["factor_projected"](n,order_divisor=minus_divisor)
    if out["factor"]:return {**out,"path":"scalar"}
    out=factor_quadratic(n,plus_divisor)
    if out["factor"]:return {**out,"path":"quadratic"}
    factor,_,reason=SINGLE["WEIGHTED"]["factor_batched"](n,"hybrid")
    return {"status":"factor" if factor else "weighted-failure","factor":factor,
            "path":"weighted","reason":reason}

def validate():
    checks={"convolution":0,"chirp":0,"real_tilt":0,"local_colour_order":0,
            "factor":0,"tilted_factor":0}
    rng=random.Random(2026100413)
    primes=SINGLE["primes_upto"](199)
    for n,d in ((323,5),(4897,5),(1643,3)):
        ring=QuadraticRing(n,d)
        for _ in range(12):
            a=([rng.randrange(n) for _ in range(5)],[rng.randrange(n) for _ in range(5)])
            b=([rng.randrange(n) for _ in range(4)],[rng.randrange(n) for _ in range(4)])
            out=ring.poly_mul(a,b);literal=[(0,0)]*8
            for i,av in enumerate(zip(*a)):
                for j,bv in enumerate(zip(*b)):
                    literal[i+j]=ring.add(literal[i+j],ring.mul(av,bv))
            assert list(zip(*out))==literal;checks["convolution"]+=1
            inverse=pow((1-d)%n,-1,n)
            unit=((1+d)*inverse%n,2*inverse%n)
            actual=chirp(ring,a,unit,ring.power(unit,3),8)
            expected=[polynomial_value(ring,a,ring.mul(unit,ring.power(unit,3*i)))
                      for i in range(8)]
            assert actual==expected;checks["chirp"]+=1
            for width in (2,4,6):
                alpha=ring.power(unit,2)
                roots=[ring.power(alpha,i) for i in range(width)]
                poly=polynomial_tree(ring,roots)[0]
                tilted=chirp_real_tilt(ring,poly,unit,width,8)
                if tilted["factor"]:
                    assert 1<tilted["factor"]<n and n%tilted["factor"]==0
                elif tilted["fallback"]:
                    assert tilted["values"]==chirp(ring,poly,ring.power(alpha,width),ring.power(alpha,width),8)
                else:
                    for i,value in enumerate(tilted["values"]):
                        phase=ring.power(unit,width*width*(i+1)+width*(width-1)//2)
                        assert ring.mul(phase,(value,0))==polynomial_value(ring,poly,ring.power(alpha,width*(i+1)))
                checks["real_tilt"]+=1
    for i,p in enumerate(primes):
        if p==2:continue
        for q in primes[i+1:]:
            n=p*q;out=factor_quadratic(n,order_divisor=1)
            if out["factor"]:assert out["factor"] in (p,q),(n,out)
            else:
                assert out["status"] in ("certified-large-order","colour-unresolved",
                                         "kernel-unresolved"),(n,out)
                if out["status"]=="certified-large-order":
                    d=out["discriminant"];a=tuple(out["projected_base"])
                    local=[]
                    for prime in (p,q):
                        r=QuadraticRing(prime,d)
                        period=prime-int(gmpy2.legendre(d,prime))
                        assert r.power(a,period)==(1,0)
                        assert all(r.power(a,k)!=(1,0)
                                   for k in range(1,out["certified_through"]+1))
                        from sympy import factorint
                        for factor,e in factorint(period).items():
                            for _ in range(e):
                                if r.power(a,period//factor)==(1,0):period//=factor
                                else:break
                        local.append(period)
                    assert math.gcd(*local)==1,(n,out,local)
                    checks["local_colour_order"]+=1
            checks["factor"]+=1
            # Also exercises same-colour N-1 cases, including the split
            # quadratic algebra, rather than assuming Jacobi=-1 throughout.
            tilted=factor_quadratic(n,order_divisor=1,tilted=True,discriminant=-1)
            if tilted["factor"]:assert tilted["factor"] in (p,q),(n,tilted)
            elif tilted["status"]=="certified-large-order":
                ring=QuadraticRing(n,tilted["discriminant"])
                alpha=ring.power(tuple(tilted["projected_base"]),2)
                for prime in (p,q):
                    local=QuadraticRing(prime,tilted["discriminant"])
                    assert all(local.power(alpha,k)!=(1,0) for k in range(1,tilted["certified_through"]+1))
            else:assert tilted["status"] in ("colour-unresolved","kernel-unresolved"),(n,tilted)
            checks["tilted_factor"]+=1
    safe= factor_quadratic(4897,order_divisor=1)
    assert safe["factor"] in (59,83)
    return checks

def benchmark(bits_list,cases,seed,repeats):
    rng=random.Random(seed);scheduler=random.Random(seed^0x631D)
    rows=[]
    for bits in bits_list:
        pool=[]
        for _ in range(cases):
            lo=1<<(bits//2-1);hi=(1<<(bits//2))-200
            p=int(gmpy2.next_prime(rng.randrange(lo,hi)));q=int(gmpy2.next_prime(rng.randrange(lo,hi)))
            if p==q:q=int(gmpy2.next_prime(q+2))
            pool.append((min(p,q),max(p,q)))
        totals={k:[] for k in ("weighted","scalar-hybrid","colour-hybrid","quadratic","quadratic-tilted")}
        hits=0;extra=0;paths={}
        for p,q in pool:
            n=p*q
            def weighted():
                f,_,why=SINGLE["WEIGHTED"]["factor_batched"](n,"hybrid")
                return {"factor":f,"path":"weighted","reason":why}
            methods={"weighted":weighted,
                     "scalar-hybrid":lambda:SINGLE["factor_hybrid"](n,16),
                     "colour-hybrid":lambda:factor_hybrid_colour(n),
                     "quadratic":lambda:factor_quadratic(n),
                     "quadratic-tilted":lambda:factor_quadratic(n,tilted=True)}
            per={k:[] for k in methods};outs={}
            for _ in range(repeats):
                names=list(methods);scheduler.shuffle(names)
                for name in names:
                    began=time.perf_counter();out=methods[name]();elapsed=time.perf_counter()-began
                    if out["factor"]:assert out["factor"] in (p,q),(n,name,out)
                    if not name.startswith("quadratic"):assert out["factor"] is not None,(n,name,out)
                    outs[name]=out;per[name].append(elapsed*1000)
            for name,ts in per.items():totals[name].append(statistics.mean(ts))
            hits+=outs["quadratic"]["factor"] is not None
            extra+=outs["colour-hybrid"]["path"]=="quadratic"
            path=outs["colour-hybrid"]["path"];paths[path]=paths.get(path,0)+1
        rows.append({"nominal_bits":bits,"cases":cases,"quadratic_solved":hits,
                     "additional_colour_solved":extra,"hybrid_paths":paths,
                     "median_ms":{k:statistics.median(ts) for k,ts in totals.items()},
                     "total_ms":{k:sum(ts) for k,ts in totals.items()},
                     "inputs_decimal":[str(p*q) for p,q in pool]})
    return {"seed":seed,"repeats":repeats,"records":rows,
            "protocol":"Actual full calls; shuffled order; no cross-input caches; own Python baseline."}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command",choices=("validate","factor","hybrid","benchmark"))
    parser.add_argument("n",type=int,nargs="?")
    parser.add_argument("--order-divisor",type=int,default=256)
    parser.add_argument("--tilt",action="store_true",help="exact real-coordinate chirp; factor command only")
    parser.add_argument("--discriminant",type=int,help="explicit public quadratic colour; factor command only")
    parser.add_argument("--bits",type=int,nargs="+",default=[48,64,80])
    parser.add_argument("--cases",type=int,default=24)
    parser.add_argument("--repeats",type=int,default=3)
    parser.add_argument("--seed",type=int,default=2026100461)
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    if args.command=="validate":out={"checks":validate()}
    elif args.command=="benchmark":out=benchmark(args.bits,args.cases,args.seed,args.repeats)
    else:
        if args.n is None:parser.error("N required")
        out=factor_quadratic(args.n,args.order_divisor,args.tilt,args.discriminant) if args.command=="factor" else factor_hybrid_colour(args.n,plus_divisor=args.order_divisor)
    out["source_sha256"]=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    encoded=json.dumps(out,indent=2)+"\n"
    if args.output:args.output.write_text(encoded)
    print(encoded,end="")

if __name__=="__main__":main()
