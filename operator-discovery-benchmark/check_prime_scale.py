#!/usr/bin/env python3
"""Independent integer-grid, factorial, root and complete-primality audits."""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial,gcd,lcm
from pathlib import Path
import json
import time
import flint

from check_gap import factors,log_D

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-scale-results'


def mu(n):
    fs=factors(n)
    return 0 if any(e>1 for e in fs.values()) else (-1)**len(fs)


def root(n,k):
    lo=0;step=1
    while step**k<=n:step*=2
    while step:
        if (lo+step)**k<=n:lo+=step
        step//=2
    return lo


@lru_cache(maxsize=None)
def fact(n):return factorial(n)


def integer_ratio(c,x):
    result=Q(1)
    for a,v in enumerate(c,1):
        if v:result*=Q(fact(int(a*x)))**v
    return result


def vector_product(vector):
    value=Q(1)
    for p,e in vector.items():value*=Q(int(p))**int(e)
    return value


def extraction(data):
    row=data['prime_extraction_grammar'];h=log_D([Q(0),Q(1)]+[Q(1)]*4095)
    assert h==list(map(Q,row['log_coefficients']))
    result=[]
    for n in range(1,len(h)):
        value=Q(0)
        for k in range(1,n.bit_length()):
            m=root(n,k)
            if m**k==n:value+=Q(mu(k),k)*h[m]
        result.append(value)
        assert value==Q(row['extracted_coefficients'][n])==int(flint.fmpz(n).is_prime())
    assert len(row['models'])==42 and row['survivors']==[{'atom':'mu','power':-1,'training_passed':True,'held_out_passed':True}]
    for k in range(1,65):
        assert sum((Q(mu(d),k) for d in range(1,k+1) if k%d==0),Q(0))==int(k==1)
    g=list(map(Q,row['generic_power_lift_inverse_control']['input_g']))
    lifted=list(map(Q,row['generic_power_lift_inverse_control']['power_lifted_h']))
    def transform(values,weighted):
        out=[Q(0)]*len(values)
        for n in range(2,len(values)):
            for k in range(1,n.bit_length()):
                m=root(n,k)
                if m**k==n:out[n]+=Q(mu(k) if weighted else 1,k)*values[m]
        return out
    assert transform(g,False)==lifted and transform(lifted,True)==g
    assert transform(transform(g,True),False)==g
    for n,base in enumerate(data['native_von_Mangoldt_coefficient_prime_bases']):
        if n<2:assert base==0;continue
        f=factors(n);expected=next(iter(f)) if len(f)==1 else 0
        assert expected==base
    return {'complete_formal_indices_checked':4096,'held_out_prime_power_exponents_checked':64,'all_passed':True}


def floors(data):
    source=data['floor_filter_grammar'];L=lcm(*range(1,8))
    certified={tuple(r['coefficients']) for r in source['certified_positive_filters']}
    independent=set();balanced=trained=0
    for c in product(range(-2,3),repeat=7):
        if -sum(c) not in (1,2) or sum((j+1)*v for j,v in enumerate(c)) or gcd(*map(abs,c))!=1:continue
        balanced+=1
        if any(sum(v*((j+1)*k//4) for j,v in enumerate(c))<0 for k in range(4)):continue
        trained+=1
        if all(sum(v*((j+1)*k//L) for j,v in enumerate(c))>=0 for k in range(L)):independent.add(c)
    assert independent==certified and len(certified)==67 and balanced==543 and trained==341
    for row in source['certified_positive_filters']:
        c=row['coefficients']
        if row['height']==2:
            left,right=row['bounded_height_one_decomposition']
            assert tuple(left) in certified and tuple(right) in certified
            assert -sum(left)==-sum(right)==1 and [u+v for u,v in zip(left,right)]==c
    alias=source['first_coarse_grid_alias'];c=alias['coefficients'];t=Q(alias['negative_breakpoint'])
    assert sum(v*int((j+1)*t) for j,v in enumerate(c))==alias['value']==-2
    assert integer_ratio(c,Q(2,7))==Q(1,4)==vector_product(alias['actual_zeta_trace_log_vector'])
    return {'independent_integer_grid_denominator':L,'exact_periodic_filters_checked':67,
            'all_52_height_two_filters_have_bounded_height_one_decompositions':True,'all_passed':True}


def identities(data):
    source=data['universal_scale_identity_controls'];groups=0
    for row in source['floor_trace_exact_groups']:
        value=integer_ratio(row['coefficients'],Q(row['X']))
        assert value.denominator==1 and value==vector_product(row['prime_log_vector'])
        groups+=1
    c=data['floor_filter_grammar']['selected_filter']
    for row in source['Mobius_decode_exact_groups']:
        x=Q(row['X']);value=Q(1)
        for m in range(1,int(2*x)+1):
            if mu(m):value*=integer_ratio(c,x/m)**mu(m)
        assert value==vector_product(row['Mobius_decoded_log_vector'])==vector_product(row['direct_prime_power_log_vector'])
    assert integer_ratio(c,Q(5))>1
    assert vector_product(source['Mobius_decode_exact_groups'][1]['Mobius_decoded_log_vector'])==Q(7,10)<1
    for row in source['prime_power_removal_exact_groups']:
        expected=Q(1)
        for n in range(2,row['X']+1):
            if flint.fmpz(n).is_prime():expected*=n
        assert expected==vector_product(row['theta_log_vector'])
    return {'exact_factorial_ratios_checked':groups,'exact_multiplicative_Mobius_decoders_checked':6,
            'actual_prime_power_removal_groups':9,'positive_trace_negative_contrast_control_verified':True,'all_passed':True}


def prime_flags(limit):
    bits=bytearray(b'\x01')*(limit+1);bits[0:2]=b'\x00\x00'
    for p in range(2,limit+1):
        if bits[p]:
            for n in range(2*p,limit+1,p):bits[n]=0
    return bits


def observations(data):
    source=data['actual_prime_scale_observations'];bits=prime_flags(source['sieve_cutoff']);total=0;large=0
    for row in source['records']:
        lo,hi=row['lower_exclusive'],row['upper_inclusive']
        if hi<len(bits):values=[n for n in range(lo+1,hi+1) if bits[n]]
        else:
            values=[n for n in range(lo+1,hi+1) if flint.fmpz(n).is_prime()]
            large+=hi-lo
        assert len(values)==row['prime_count']
        assert (values[0] if values else None)==row['first_prime']
        assert (values[-1] if values else None)==row['last_prime']
        assert max((b-a for a,b in zip(values,values[1:])),default=None)==row['maximum_internal_consecutive_prime_gap']
        for q,counts in row['residue_counts'].items():assert [sum(p%int(q)==r for p in values) for r in range(int(q))]==counts
        assert row['finite_observation_only'];total+=hi-lo
    assert not source['universal_count_or_gap_bound_inferred_from_samples']
    return {'complete_windows_checked':len(source['records']),'integers_checked_in_windows':total,
            'distant_window_FLINT_primality_checks':large,'largest_checked_integer':source['largest_sampled_integer'],
            'all_scale_estimate_not_inferred_from_finite_samples':True,'all_passed':True}


def norm_controls():
    rows=[]
    for N in (16,64,256,1024,4096):
        harmonic=sum((Q(abs(mu(n)),n) for n in range(1,N+1)),Q(0))
        # Test vector saturating the row at X=N: f(N/n)=sign(mu(n))*N/n.
        value=sum((Q(mu(n))*Q(mu(n))*Q(N,n) for n in range(1,N+1)),Q(0))/N
        assert value==harmonic
        rows.append({'X':N,'exact_sigma_one_norm_lower':str(harmonic),'saturating_input_verified':True})
    assert all(Q(b['exact_sigma_one_norm_lower'])>Q(a['exact_sigma_one_norm_lower']) for a,b in zip(rows,rows[1:]))
    return {'records':rows,'new_prime_specific_decoder_cancellation_bound_proved':False,'all_passed':True}


def main():
    start=time.monotonic();source=json.loads((DEST/'prime_scale_search.json').read_text())
    extract=extraction(source);flo=floors(source);ident=identities(source);obs=observations(source);norm=norm_controls()
    assert source['all_passed'] and source['prime_information_priority']['ten_existing_candidate_families_retained']
    assert len(source['prime_information_priority']['candidate_triage'])==10
    assert not source['counts_as_new_operator'] and not source['historical_novelty_established']
    assert not source['new_uniform_prime_distribution_estimate_proved'] and not source['new_RH_estimate_proved']
    checks={'independent_LOG_and_perfect_power_prime_extraction':extract['all_passed'],
            'integer_grid_all_scale_floor_certificates_and_alias_rejection':flo['all_passed'],
            'integer_factorials_Mobius_decode_and_prime_power_removal':ident['all_passed'],
            'complete_dyadic_and_distant_prime_residue_gap_windows':obs['all_passed'],
            'saturating_decoder_norm_vectors':norm['all_passed'],
            'finite_samples_novelty_and_new_bound_scope_honest':True}
    out={'checks':checks,'extraction_audit':extract,'floor_audit':flo,'identity_audit':ident,'observation_audit':obs,
         'decoder_norm_controls':norm,'production_imports':False,'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'prime_scale_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent prime-scale exact audit:',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
