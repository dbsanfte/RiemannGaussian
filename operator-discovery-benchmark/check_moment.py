#!/usr/bin/env python3
"""Independent valuation-residue fibres, Pascal weights and Omega EXP audit."""

from fractions import Fraction as Q
from functools import lru_cache
from math import factorial, isqrt
from pathlib import Path
import json
import time
import flint

from check_gap import factors, divisors, omega, exp_D, log_D, D

BASE=Path(__file__).resolve().parent
DEST=BASE/'moment-results'


@lru_cache(maxsize=None)
def weights(m):
    w=[1]
    for _ in range(m):
        w=[(w[j] if j<len(w) else 0)-(w[j-1] if j else 0) for j in range(len(w)+1)]
    return tuple(w)


def root(n,r):
    v,exact=flint.fmpz(n).root(r),None
    v=int(v)
    return v if v**r==n else None


@lru_cache(maxsize=None)
def fibres(n,m,gap_min=2):
    fs=factors(n)
    r=m+2
    visible={p:e%r for p,e in fs.items() if e%r}
    out=[]
    if len(visible)==2:
        p,q=sorted(visible)
        a,b=visible[p],visible[q]
        if a+b==m and fs[p]==a and fs[q]==b:
            d=root(n//(p**a*q**b),r)
            if d is not None and d>=gap_min and q-p==d:
                out.append((p,q,b,weights(m)[b]))
    elif len(visible)==1:
        p,e=next(iter(visible.items()))
        if e==m and fs[p]==m:
            d=root(n//p**m,r)
            if d is not None and d>=gap_min:
                for q in (p-d,p+d):
                    if q>=2 and flint.fmpz(q).is_prime():
                        a,b=sorted((p,q))
                        j=0 if p==a else m
                        out.append((a,b,j,weights(m)[j]))
    return tuple(sorted(out))


def correction(h,m):
    # Enumerate a superset of possible indices, then decode rather than
    # accumulate forward binomial images. This is independent of production.
    support=sorted(p for p,v in h.items() if v and flint.fmpz(p).is_prime())
    possible={a**(m-j)*b**j*(b-a)**(m+2)
              for a in support for b in support if b-a>=2 for j in range(m+1)}
    out={n:sum((Q(c)*h.get(a,Q(0))*h.get(b,Q(0)) for a,b,j,c in fibres(n,m)),Q(0)) for n in possible}
    return {n:v for n,v in out.items() if v}


def flow(h,t,m):
    K=correction(h,m)
    return {n:v for n in h.keys()|K.keys() if (v:=h.get(n,Q(0))+t*K.get(n,Q(0)))}


def exp_query(h,n):
    @lru_cache(maxsize=None)
    def E(k):
        if k==1:
            return Q(1)
        return sum((omega(d)*h.get(d,Q(0))*E(k//d) for d in divisors(k) if d>1 and h.get(d,Q(0))),Q(0))/omega(k)
    return E(n)


def audit_generic(data):
    queries=0
    for row in data['generic_shear_laws']['records']:
        m=row['m'];h={int(n):Q(v) for n,v in row['input_log'].items()}
        K=correction(h,m)
        assert K=={int(n):Q(v) for n,v in row['correction'].items()}
        t,u=Q(2,3),Q(-3,5)
        assert flow(flow(h,t,m),u,m)==flow(h,t+u,m)
        assert flow(flow(h,t,m),-t,m)==h
        assert correction({n:v/2 for n,v in h.items()},m)=={n:v/4 for n,v in K.items()}
        assert all(not flint.fmpz(n).is_prime() for n in K)
        n0=4*6**m
        assert min(K)==row['first_index']==n0 and K[n0]==h[3]*h[5]
        assert exp_query(h,n0)==Q(row['first_original_EXP_coefficient'])
        assert exp_query(flow(h,t,m),n0)==Q(row['first_transformed_EXP_coefficient'])
        queries+=2
    small=data['generic_shear_laws']['dense_ordinary_EXP_check']
    h={2:Q(-2,3),3:Q(3,5),5:Q(-1,7),7:Q(2,9),11:Q(1,4)}
    K=correction(h,2);N=small['cutoff']
    log=[h.get(n,Q(0)) for n in range(N+1)];extra=[K.get(n,Q(0)) for n in range(N+1)]
    result=exp_D([a+b for a,b in zip(log,extra)])
    assert result==list(map(Q,small['output']))
    assert log_D(result)==[a+b for a,b in zip(log,extra)]
    pin=exp_D([a/2+b/4 for a,b in zip(log,extra)])
    pout=exp_D([a/2+b/2 for a,b in zip(log,extra)])
    assert pin==list(map(Q,small['input_half_root_output']))
    assert pout==list(map(Q,small['output_half_root'])) and pin!=pout
    assert D(pout,pout)==result
    return {'independent_sparse_EXP_coefficient_queries':queries,'all_passed':True}


def audit_zeta(data):
    sparse,dense,collisions=0,0,0
    for row in data['finite_prime_input_zeta_profiles']:
        m=row['m'];N=row['prime_input_cutoff']
        for n,v in row['finite_prime_input_coefficients'].items():
            n=int(n)
            fs=[(a,b,j,c) for a,b,j,c in fibres(n,m) if b<=N]
            assert sum(c for a,b,j,c in fs)==Q(v)
            assert (Q(v)>0)==(isqrt(n)**2==n)
            sparse+=1
            collisions+=int(len(fs)>1)
        assert row['first_index']==4*6**m and row['first_coefficient']=='1'
    for row in data['complete_zeta_prefixes']:
        for n in range(2,row['encoded_cutoff']+1):
            assert sum(c for a,b,j,c in fibres(n,row['m']))==Q(row['coefficients'].get(str(n),'0'))
            dense+=1
    # Full factor certificates at indices larger than machine words.
    assert any(int(n)>2**64 for row in data['finite_prime_input_zeta_profiles'] for n in row['finite_prime_input_coefficients'])
    assert not fibres(4*6**8-1,8)
    assert fibres(4*6**8,8)==((3,5,0,1),)
    return {'finite_prime_input_encoded_queries':sparse,'complete_prefix_indices_checked':dense,
            'aggregated_diagonal_fibres_encountered':collisions,'arbitrary_precision_indices_checked':True,
            'all_passed':True}


def audit_grammar(data):
    for row in data['moment_annihilation_grammar']['bounded_search']:
        m=row['m']
        assert row['held_out_survivors']==[list(weights(m))]
    for row in data['moment_annihilation_grammar']['higher_order_linear_constraint_checks']:
        m=row['m'];w=weights(m)
        assert list(map(Q,row['weights']))==list(w)
        assert all(sum(w[j]*j**k for j in range(m+1))==0 for k in range(m))
        assert sum(w[j]*j**m for j in range(m+1))==factorial(m)==Q(row['first_nonzero_moment'])
    image=data['image_scale_fit'];first={row['m']:row['first_index'] for row in data['finite_prime_input_zeta_profiles']}
    fits=[{'A':A,'B':B,'held_out_passed':all(A*B**m==first[m] for m in (8,12,16))}
          for A in range(1,17) for B in range(2,17) if all(A*B**m==first[m] for m in (2,4,6))]
    assert fits==image['fits']==[{'A':4,'B':6,'held_out_passed':True}]
    # Independent certified half-line envelopes for the floating discovery
    # records. No universal claim is made for the unselected masks.
    flint.ctx.prec=160
    for row in data['gap_support_mask_grammar']['records']:
        g=row['gap_minimum']
        for split in ('training','held_out'):
            obs=row[split];ps=tuple(n for n in range(2,obs['prime_cutoff']+1) if flint.fmpz(n).is_prime())
            a,b=obs['maximizing_edge']
            def envelope(p,q):
                return (flint.arb(1)/(p*(q-p))).sqrt()+(flint.arb(1)/(q*(q-p))).sqrt()
            top=envelope(a,b);assert b-a>=g
            for p in ps:
                for q in ps:
                    if q-p>=g and (p,q)!=(a,b):assert envelope(p,q)<top
            assert bool(top<1)==obs['envelope_below_one']
            assert obs['edges_removed']==sum(1 for p in ps for q in ps if 0<q-p<g)
    assert data['gap_support_mask_grammar']['smallest_stable_gap_mask']==2
    return True


def main():
    start=time.monotonic();data=json.loads((DEST/'moment_search.json').read_text());assert data['all_passed']
    generic,zeta=audit_generic(data),audit_zeta(data)
    checks={'Pascal_independent_moment_annihilation':audit_grammar(data),
            'complete_prime_valuation_residue_fibres':zeta['all_passed'],
            'full_sparse_shear_group_and_Omega_EXP_queries':generic['all_passed'],
            'critical_strip_correction_domains_kept_distinct':data['ordinary_correction_absolute_domain_proved']=='Re(s)>1/m' and data['paired_correction_domain_proved']=='Re(s)>1/(m+1)',
            'novelty_and_RH_solution_not_claimed':not data['historical_novelty_established'] and not data['new_RH_estimate_proved']}
    out={'checks':checks,'zeta_audit':zeta,'generic_audit':generic,'production_imports':False,
         'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'moment_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent moment exact audit:',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)
    assert out['all_passed']


if __name__=='__main__':
    main()
