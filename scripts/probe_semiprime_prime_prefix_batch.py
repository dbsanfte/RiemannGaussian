#!/usr/bin/env python3
"""Independent prime-prefix cache with sparse accumulating remainder queries.

Optional research replay; not part of Lean builds or ordinary CI.
Run from formal/ with ../.venv/bin/python -B scripts/probe_semiprime_prime_prefix_batch.py.
Generated factor labels are used only to verify returned factors.
"""

import math,json,random,time,statistics,bisect
import gmpy2
def primes_upto(M):
    s=bytearray(b'\x01')*(M+1)
    s[0:2]=b'\x00\x00'
    for p in range(2,math.isqrt(M)+1):
        if s[p]:
            start=p*p;s[start:M+1:p]=b'\x00'*((M-start)//p+1)
    return [p for p in range(2,M+1) if s[p]]
class PrimePrefixCache:
    def __init__(self,M):
        if M < 2: raise ValueError('cache bound must include prime 2')
        self.M=M;self.ps=primes_upto(M);count=len(self.ps)
        L=1<<(count-1).bit_length();self.L=L
        self.V=[gmpy2.mpz(1)]*(2*L)
        for i,p in enumerate(self.ps):self.V[L+i]=gmpy2.mpz(p)
        for k in range(L-1,0,-1):self.V[k]=self.V[2*k]*self.V[2*k+1]
    def batch(self,inputs):
        L=self.L;mod=[gmpy2.mpz(1)]*(2*L);ends={}
        for idx,n in enumerate(inputs):
            m=math.isqrt(n)
            if m>self.M:raise ValueError("cache too small")
            count=bisect.bisect_right(self.ps,m)
            if not count:raise ValueError("invalid semiprime")
            node=L+count-1
            mod[node]*=n;ends.setdefault(node,[]).append((idx,n))
        for k in range(L-1,0,-1):mod[k]=mod[2*k]*mod[2*k+1]
        factors=[None]*len(inputs);visited=0
        def walk(k,a):
            nonlocal visited
            if mod[k]==1:return
            visited+=1
            if k>=L:
                aa=a*self.V[k]
                for idx,n in ends[k]:
                    g=math.gcd(int(aa%n),n)
                    assert 1<g<n and n%g==0
                    factors[idx]=tuple(sorted((g,n//g)))
                return
            le,ri=2*k,2*k+1
            if mod[le]!=1:walk(le,a%mod[le])
            if mod[ri]!=1:
                m=mod[ri]
                walk(ri,(a%m)*(self.V[le]%m)%m)
        if inputs: walk(1,gmpy2.mpz(1))
        return factors,visited
    def size_bits(self):return sum(int(x.bit_length()) for x in self.V)

class SparsePrimePrefixCache(PrimePrefixCache):
    def batch(self,inputs):
        L=self.L;mod={};ends={};needed=set()
        for idx,n in enumerate(inputs):
            if n < 4 or math.isqrt(n) > self.M:
                raise ValueError('semiprime outside cache bound')
            count=bisect.bisect_right(self.ps,math.isqrt(n))
            if not count: raise ValueError('invalid semiprime')
            node=L+count-1;mod[node]=mod.get(node,gmpy2.mpz(1))*n
            ends.setdefault(node,[]).append((idx,n))
            while node:
                needed.add(node);node//=2
        for k in sorted(needed,reverse=True):
            if k<L:mod[k]=mod.get(2*k,gmpy2.mpz(1))*mod.get(2*k+1,gmpy2.mpz(1))
        factors=[None]*len(inputs);visited=0
        def walk(k,a):
            nonlocal visited
            visited+=1
            if k>=L:
                aa=a*self.V[k]
                for idx,n in ends[k]:
                    g=math.gcd(int(aa%n),n)
                    assert 1<g<n and n%g==0
                    factors[idx]=tuple(sorted((g,n//g)))
                return
            le,ri=2*k,2*k+1
            if le in mod:walk(le,a%mod[le])
            if ri in mod:walk(ri,(a%mod[ri])*(self.V[le]%mod[ri])%mod[ri])
        if inputs: walk(1,gmpy2.mpz(1))
        return factors,visited


def replay():
    import runpy
    from pathlib import Path
    existing=runpy.run_path(str(Path(__file__).with_name('probe_semiprime_modular_signal.py')))['factor_semiprime']
    # Small exhaustive gate includes squares, unbalanced pairs, repeated queries
    # and the empty batch; factors are never supplied to the cache.
    small_primes = primes_upto(199)
    pairs0 = [(p, q) for i, p in enumerate(small_primes)
              for q in small_primes[i:]]
    nums0 = [p*q for p, q in pairs0]
    cache0 = SparsePrimePrefixCache(math.isqrt(max(nums0)))
    assert cache0.batch(nums0)[0] == pairs0
    assert cache0.batch([4, 6, 4, 9, 6])[0] == [(2, 2), (2, 3), (2, 2), (3, 3), (2, 3)]
    assert cache0.batch([]) == ([], 0)
    try:
        cache0.batch([(cache0.M + 1)**2])
    except ValueError:
        pass
    else:
        raise AssertionError('cache-bound check failed')
    print(json.dumps({'exhaustive_prime_prefix_checks': len(nums0),
                      'duplicate_empty_bound_checks': True}), flush=True)
    rng=random.Random(6897333);bits=32
    pool=primes_upto((1<<(bits//2))-1)
    pool=[p for p in pool if p>=1<<(bits//2-1)];rng.shuffle(pool)
    pairs=[tuple(sorted((pool[2*i],pool[2*i+1]))) for i in range(1024)]
    nums=[p*q for p,q in pairs]
    t=time.perf_counter();cache=SparsePrimePrefixCache((1<<(bits//2))-1);prep=time.perf_counter()-t
    for T in [1,64,256,1024]:
        modes=['table','plain','prime-power'];timings={m:[] for m in modes}
        for repeat in range(3):
            rng.shuffle(modes)
            for mode in modes:
                t=time.perf_counter()
                if mode=='table':
                    fs,vis=cache.batch(nums[:T]);assert fs==pairs[:T]
                else:
                    for n,pair in zip(nums[:T],pairs[:T]):
                        f=existing(n,variant=mode).factor
                        assert f in pair,(mode,n,f,pair)
                timings[mode].append(time.perf_counter()-t)
        med={k:statistics.median(ts) for k,ts in timings.items()}
        print(json.dumps({"max_bits":bits,"batch":T,"cache_build_ms":round(prep*1000,4),
          "median_us_per_input":{k:round(v*1e6/T,4) for k,v in med.items()},
          "table_including_build_us_per_input":round((prep+med['table'])*1e6/T,4),
          "value_tree_bytes":(cache.size_bits()+7)//8}),flush=True)


if __name__ == '__main__':
    replay()
