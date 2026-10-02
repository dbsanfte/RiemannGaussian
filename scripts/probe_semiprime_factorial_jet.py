#!/usr/bin/env python3
"""Exact factorial value/derivative batching for odd semiprimes.

Optional research replay; not part of Lean builds or ordinary CI.
Run from formal/ with ../.venv/bin/python -B scripts/probe_semiprime_factorial_jet.py.
Generated factor labels are used only to verify returned factors.
"""

import math,json,random,time
import gmpy2
from sympy import primerange
class FactorialJetCache:
    def __init__(self,M):
        if M < 1: raise ValueError('positive cache bound required')
        self.M=M;L=1<<(M-1).bit_length();self.L=L
        self.V=[gmpy2.mpz(1)]*(2*L)
        self.D=[gmpy2.mpz(0)]*(2*L)
        for k in range(1,M+1):
            self.V[L+k-1]=gmpy2.mpz(k);self.D[L+k-1]=gmpy2.mpz(1)
        for k in range(L-1,0,-1):
            a,c=self.V[2*k],self.V[2*k+1]
            b,d=self.D[2*k],self.D[2*k+1]
            self.V[k]=a*c;self.D[k]=a*d+b*c
    def batch(self,inputs):
        L=self.L;mod=[gmpy2.mpz(1)]*(2*L);ends={}
        for idx,n in enumerate(inputs):
            m=math.isqrt(2*n)
            if m>self.M:raise ValueError("cache too small")
            node=L+m-1
            mod[node]*=n*n;ends.setdefault(node,[]).append((idx,n,m))
        for k in range(L-1,0,-1):mod[k]=mod[2*k]*mod[2*k+1]
        residues=[None]*len(inputs)
        visited=0
        def walk(k,a,b):
            nonlocal visited
            if mod[k]==1:return
            visited+=1
            if k>=L:
                z=k-L+1
                aa=a*z;bb=b*z+a
                for idx,n,m in ends[k]:
                    residues[idx]=(int(aa%(n*n)),int(bb%n))
                return
            le,ri=2*k,2*k+1
            if mod[le]!=1:walk(le,a%mod[le],b%mod[le])
            if mod[ri]!=1:
                m=mod[ri];v=self.V[le]%m;d=self.D[le]%m
                walk(ri,(a%m)*v%m,((a%m)*d+(b%m)*v)%m)
        walk(1,gmpy2.mpz(1),gmpy2.mpz(0))
        factors=[];branches={"gcd":0,"trace":0}
        for n,(B,D) in zip(inputs,residues):
            g=math.gcd(B,n)
            if 1<g<n:
                p=g;q=n//g;branches["gcd"]+=1
            elif g==n:
                b=(B//n)%n
                assert math.gcd(b,n)==1,(n,b)
                S=D*pow(b,-1,n)%n
                disc=S*S-4*n;root=math.isqrt(disc)
                assert root*root==disc and (S-root)%2==0
                p=(S-root)//2;q=(S+root)//2;branches["trace"]+=1
            else:raise ValueError("non-semiprime or insufficient threshold")
            assert p*q==n and p>1 and q>1
            factors.append(tuple(sorted((p,q))))
        return factors,visited,branches
    def size_bits(self):
        return sum(int(x.bit_length()) for x in self.V+self.D)


def replay():
    rng=random.Random(631933)
    # Exhaustive small semiprimes, including squares and highly unbalanced pairs.
    ps=list(primerange(3,200))
    pairs=[(p,q) for i,p in enumerate(ps) for q in ps[i:]]
    nums=[p*q for p,q in pairs]
    cache=FactorialJetCache(max(math.isqrt(2*n) for n in nums))
    fs,visited,branches=cache.batch(nums)
    assert fs==pairs
    print(json.dumps({"exhaustive_factorial_jet_checks":len(nums),"branches":branches,
      "max_N":max(nums)}),flush=True)
    bench=[]
    for bits,counts in [(24,[16,64,120]),(28,[32,128,384]),(32,[64,256,1024])]:
        ps=list(primerange(1<<(bits//2-1),1<<(bits//2)))
        rng.shuffle(ps)
        assert 2*max(counts)<=len(ps),(bits,len(ps))
        pairs=[tuple(sorted((ps[2*i],ps[2*i+1]))) for i in range(max(counts))]
        nums=[p*q for p,q in pairs]
        M=math.isqrt(2*((1<<bits)-1))
        t=time.perf_counter();cache=FactorialJetCache(M);prep=time.perf_counter()-t
        size=cache.size_bits()
        for T in counts:
            t=time.perf_counter();fs,visited,branches=cache.batch(nums[:T]);query=time.perf_counter()-t
            assert fs==pairs[:T]
            bench.append({"max_bits":bits,"batch":T,"threshold":M,
              "cache_build_ms":round(prep*1000,3),"query_ms":round(query*1000,3),
              "total_us_per_input":round((prep+query)*1e6/T,3),
              "cached_us_per_input":round(query*1e6/T,3),
              "value_tree_data_bytes":(size+7)//8,
              "visited_nodes":visited,"branches":branches})
        print(json.dumps({"batch_benchmark":bench[-len(counts):]}),flush=True)


if __name__ == '__main__':
    replay()
