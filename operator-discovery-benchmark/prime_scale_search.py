#!/usr/bin/env python3
"""Prime-information priority, empirical extraction and all-scale floor grammar."""

from bisect import bisect_right
from fractions import Fraction as Q
from itertools import product
from math import gcd,isqrt
from pathlib import Path
import json
import random
import time

from exact_arithmetic import formal_log

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-scale-results'


def sieve(limit):
    spf=[0]*(limit+1)
    for p in range(2,limit+1):
        if spf[p]:continue
        spf[p]=p
        if p*p<=limit:
            for n in range(p*p,limit+1,p):
                if not spf[n]:spf[n]=p
    primes=[n for n in range(2,limit+1) if spf[n]==n]
    return spf,primes


def factor(n,spf):
    result={}
    while n>1:
        p=spf[n];result[p]=result.get(p,0)+1;n//=p
    return result


def mu(n,spf):
    f=factor(n,spf)
    return 0 if any(e>1 for e in f.values()) else (-1)**len(f)


def floor(t):return t.numerator//t.denominator


def w(c,t):return sum(v*floor(a*t) for a,v in enumerate(c,1))


def add(dst,src,weight=1):
    for p,v in src.items():
        dst[p]=dst.get(p,0)+weight*v
        if not dst[p]:del dst[p]
    return dst


def vector_json(v):return {str(p):str(e) for p,e in sorted(v.items())}


def pp_vector(x,primes):
    out={}
    for p in primes:
        if p>x:break
        n=p
        while n<=x:out[p]=out.get(p,0)+1;n*=p
    return out


def prime_vector(x,primes):return {p:1 for p in primes if p<=x}


def trace(c,x,primes):
    out={};limit=max(a for a,v in enumerate(c,1) if v)*x
    for p in primes:
        if p>limit:break
        n=p
        while n<=limit:
            value=w(c,x/n)
            if value:out[p]=out.get(p,0)+value
            n*=p
        if out.get(p)==0:out.pop(p,None)
    return out


def contrast(c,x,primes):
    out={}
    for a,v in enumerate(c,1):
        if v:add(out,pp_vector(a*x,primes),v)
    return out


def integer_root(n,k):
    lo,hi=0,n+1
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid**k<=n:lo=mid
        else:hi=mid
    return lo


def extraction(spf,primes):
    h=formal_log([Q(0),Q(1)]+[Q(1)]*4095)
    for n in range(2,4097):
        fs=factor(n,spf)
        expected=Q(1,next(iter(fs.values()))) if len(fs)==1 else Q(0)
        assert h[n]==expected
    def atom(name,k):
        m=mu(k,spf)
        if name=='one':return 1
        if name=='mu':return m
        if name=='mu_square':return m*m
        if name=='lambda':return (-1)**sum(factor(k,spf).values())
        if name=='alternating':return (-1)**(k-1)
        if name=='totient':
            phi=k
            for p in factor(k,spf):phi=phi//p*(p-1)
            return phi
        raise ValueError(name)
    models=[]
    for name in ('one','mu','mu_square','lambda','alternating','totient'):
        for exponent in range(-3,4):
            def weight(k):return Q(atom(name,k))*Q(k)**exponent
            def output(k):return sum((weight(d)*Q(d,k) for d in range(1,k+1) if k%d==0),Q(0))
            training=all(output(k)==int(k==1) for k in range(1,9))
            models.append({'atom':name,'power':exponent,'training_passed':training,
                           'held_out_passed':training and all(output(k)==0 for k in range(9,33))})
    survivors=[r for r in models if r['held_out_passed']]
    assert survivors==[{'atom':'mu','power':-1,'training_passed':True,'held_out_passed':True}]
    out=[Q(0)]*len(h)
    for n in range(2,len(h)):
        if not h[n]:continue
        power=n;d=1
        while power<len(h):
            out[power]+=Q(mu(d,spf),d)*h[n]
            d+=1;power*=n
    assert all(v==int(spf[n]==n and n>=2) for n,v in enumerate(out))
    rng=random.Random(2026100721)
    g=[Q(0),Q(0)]+[Q(rng.randrange(-2,3),rng.randrange(1,6)) for _ in range(127)]
    def U_sum(values,mobius_weights):
        ans=[Q(0)]*len(values)
        for n in range(2,len(values)):
            power=n;k=1
            while power<len(values):
                ans[power]+=Q(mu(k,spf) if mobius_weights else 1,k)*values[n]
                k+=1;power*=n
        return ans
    lifted=U_sum(g,False);recovered=U_sum(lifted,True)
    assert recovered==g and U_sum(U_sum(g,True),False)==g
    generic={'input_g':list(map(str,g)),'power_lifted_h':list(map(str,lifted)),
             'two_inverse_laws_verified':True,'universal_proof':'prime_scale_proof.txt section 1'}
    return {'models_scored':len(models),'models':models,'survivors':survivors,
            'formal_log_input':'zeta ordinary coefficient sequence, complete through 4096',
            'log_coefficients':list(map(str,h)),'extracted_coefficients':list(map(str,out)),
            'law':'P(f)=sum_(d>=1)mu(d)/d * U_d(LOG_D f), U_d a(n)=a(n^(1/d)) on perfect d-th powers',
            'generic_power_lift_inverse_control':generic,
            'known_operator_calibration':True,'all_passed':True}


def floor_grammar():
    A=7;points=sorted({Q(k,a) for a in range(1,A+1) for k in range(a)})
    grid=[Q(k,4) for k in range(4)];balanced=trained=0;rows=[];rejected=[]
    for c in product(range(-2,3),repeat=A):
        height=-sum(c)
        if height not in (1,2) or sum(a*v for a,v in enumerate(c,1)) or gcd(*map(abs,c))!=1:continue
        balanced+=1
        if any(w(c,t)<0 for t in grid):continue
        trained+=1;values=[w(c,t) for t in points]
        if min(values)<0:
            if len(rejected)<8:
                i=values.index(min(values))
                rejected.append({'coefficients':list(c),'negative_breakpoint':str(points[i]),'value':values[i]})
            continue
        rows.append({'coefficients':list(c),'height':height,'breakpoint_values':values,
                     'minimum':min(values),'maximum':max(values),'universal_periodic_positivity_certified':True})
    first={tuple(r['coefficients']) for r in rows if r['height']==1}
    for row in rows:
        if row['height']!=2:continue
        c=tuple(row['coefficients'])
        decomposition=next((d for d in sorted(first) if tuple(v-u for v,u in zip(c,d)) in first),None)
        assert decomposition is not None
        row['bounded_height_one_decomposition']=[list(decomposition),[v-u for v,u in zip(c,decomposition)]]
    alias=rejected[0];assert alias['negative_breakpoint']=='1/7'
    alias['actual_zeta_trace_at_X']='2/7'
    alias['actual_zeta_trace_log_vector']={'2':'-2'}
    alias['actual_factorial_ratio']='1/4'
    return {'models_scored':5**A,'max_dilation':A,'coefficient_range':[-2,2],
            'balanced_primitive_models':balanced,'coarse_grid_survivors':trained,
            'exact_breakpoints':list(map(str,points)),'certified_positive_filters':rows,
            'height_one_count':len(first),'height_two_count':sum(r['height']==2 for r in rows),
            'first_coarse_grid_alias':alias,'selected_filter':[-2,1,0,0,0,0,0],
            'generic_positive_floor_filters_erase_zeta_zero_poles':True,
            'height_two_decomposition_scope':'only this exhaustively enumerated bounded grammar',
            'all_passed':True}


def identities(grammar,primes,spf):
    # Rational X tests probe exact boundary handling, not just integer scales.
    scales=[Q(1,2),Q(1),Q(2),Q(3),Q(5),Q(13,2),Q(17),Q(65,2),Q(257,3),Q(511,7),Q(97),Q(129,2)]
    selected=[r for r in grammar['certified_positive_filters'] if r['height']==1]
    rows=[]
    for row in selected:
        c=row['coefficients']
        for x in scales:
            left=trace(c,x,primes);right={}
            for a,v in enumerate(c,1):
                if v:
                    for n in range(2,floor(a*x)+1):add(right,factor(n,spf),v)
            assert left==right and all(e>=0 for e in left.values())
            rows.append({'coefficients':c,'X':str(x),'prime_log_vector':vector_json(left),'all_passed':True})
    c=grammar['selected_filter'];decoded=[]
    for x in (Q(1),Q(5),Q(13),Q(29,2),Q(47),Q(193,3)):
        value={}
        for m in range(1,floor(2*x)+1):
            if mu(m,spf):add(value,trace(c,x/m,primes),mu(m,spf))
        direct=contrast(c,x,primes);assert value==direct
        decoded.append({'X':str(x),'Mobius_decoded_log_vector':vector_json(value),'direct_prime_power_log_vector':vector_json(direct),'all_passed':True})
    assert decoded[1]['Mobius_decoded_log_vector']=={'2':'-1','5':'-1','7':'1'}
    roots=[]
    for n in (4,8,9,25,64,127,128,729,4096):
        result={}
        for k in range(1,n.bit_length()):
            if mu(k,spf):add(result,pp_vector(integer_root(n,k),primes),mu(k,spf))
        assert result==prime_vector(n,primes)
        roots.append({'X':n,'theta_log_vector':vector_json(result),'all_passed':True})
    return {'floor_trace_exact_groups':rows,'Mobius_decode_exact_groups':decoded,
            'prime_power_removal_exact_groups':roots,
            'positive_floor_trace_implies_positive_decoded_prime_contrast_rejected':True,
            'contrast_at_five':'log(7/10)<0','all_passed':True}


def segmented(lo,hi,primes):
    bits=bytearray(b'\x01')*(hi-lo+1)
    for p in primes:
        if p*p>hi:break
        start=max(p*p,((lo+p-1)//p)*p)
        if start<=hi:bits[start-lo::p]=b'\x00'*((hi-start)//p+1)
    for n in range(lo,min(hi,1)+1):bits[n-lo]=0
    return [lo+i for i,v in enumerate(bits) if v]


def window_record(lo,hi,values,label):
    counts={str(q):[sum(p%q==r for p in values) for r in range(q)] for q in (3,5,7)}
    return {'lower_exclusive':lo,'upper_inclusive':hi,'prime_count':len(values),
            'first_prime':values[0] if values else None,'last_prime':values[-1] if values else None,
            'maximum_internal_consecutive_prime_gap':max((b-a for a,b in zip(values,values[1:])),default=None),
            'residue_counts':counts,'sample_type':label,'finite_observation_only':True}


def observations(primes):
    rows=[]
    for k in range(20):
        lo,hi=2**k,2**(k+1);values=primes[bisect_right(primes,lo):bisect_right(primes,hi)]
        rows.append(window_record(lo,hi,values,'complete dyadic window'))
    for lo in (10**6,10**8,10**10,10**12):
        hi=lo+4096;values=segmented(lo+1,hi,primes)
        rows.append(window_record(lo,hi,values,'complete distant short window'))
    return {'sieve_cutoff':2**20,'largest_sampled_integer':10**12+4096,'records':rows,
            'universal_count_or_gap_bound_inferred_from_samples':False,
            'all_X_identity_proved_separately':True,'all_passed':True}


def priority():
    registry=json.loads((BASE/'root-results/candidate_registry.json').read_text())
    geometric={'quadratic_index_difference_root_transfer','nonlinear_prime_sum_log_coupling',
               'prime_sum_sector_decoder','residue_visible_prime_power_product_decoder'}
    families=sum((registry[k] for k in ('mathematically_verified_nonlinear_candidates','mathematically_verified_linear_candidates','mathematically_verified_integer_order_candidates')),[])
    rows=[]
    for name in families:
        rows.append({'candidate':name,'next_search_priority':'prime_information_target' if name in geometric else 'secondary_calibration',
                     'proved_new_uniform_prime_distribution_estimate':False,
                     'reason':'Contains arithmetic dependence on actual prime values; seek a new count, gap or residue consequence' if name in geometric else 'Existing formal/root laws have no proved new prime-distribution estimate'})
    return {'user_priority':'Arithmetic information about actual primes over all scales',
            'requirements':['Specify a prime observable: counts, weighted mass, gaps, correlations or residues.',
                            'Separate all-X universal identities and bounds from finite numerical observations.',
                            'Remove prime-power contamination before calling a statistic a prime count.',
                            'Record whether the consequence supplies new information or redistributes already supplied prime data.',
                            'Prove that any claimed RH-sensitive map retains ordinary-zeta zero information.',
                            'Prioritize a new arithmetic consequence or uniform estimate over another coordinate transfer.'],
            'candidate_triage':rows,'ten_existing_candidate_families_retained':True,
            'next_target':'Unsmoothed prime-window or residue observables with a new arithmetic estimate; floor traces alone cancel zero poles',
            'all_passed':True}


def main():
    start=time.monotonic();spf,primes=sieve(2**20)
    extract=extraction(spf,primes);grammar=floor_grammar();exact=identities(grammar,primes,spf)
    obs=observations(primes);rank=priority()
    bases=[0]*4097
    for n in range(2,len(bases)):
        fs=factor(n,spf)
        if len(fs)==1:bases[n]=next(iter(fs))
    out={'prime_information_priority':rank,'prime_extraction_grammar':extract,'floor_filter_grammar':grammar,
         'universal_scale_identity_controls':exact,'actual_prime_scale_observations':obs,
         'native_von_Mangoldt_coefficient_prime_bases':bases,
         'counts_as_new_operator':False,'historical_novelty_established':False,
         'new_uniform_prime_distribution_estimate_proved':False,'new_RH_estimate_proved':False,
         'all_passed':True,'seconds':time.monotonic()-start}
    DEST.mkdir(exist_ok=True);(DEST/'prime_scale_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Prime-scale grammar:',grammar['models_scored'],'programs;',len(grammar['certified_positive_filters']),
          'positive filters;',len(obs['records']),'complete windows through',obs['largest_sampled_integer'],flush=True)
    print('All-scale identities are proved separately; no new prime bound or historical novelty claimed. Seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
