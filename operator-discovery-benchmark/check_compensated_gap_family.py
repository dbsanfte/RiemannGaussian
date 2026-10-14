#!/usr/bin/env python3
"""Independent all-case audits of the frozen family certificate experiment."""
from fractions import Fraction as Q
from itertools import product
from math import comb,gcd
from pathlib import Path
from collections import Counter
import hashlib
import json
import flint

from check_compensated_global_gap import homogeneous,primitive,mul,add,scale,factor,divisors,mu

BASE=Path(__file__).resolve().parent
DEST=BASE/'compensated-shift-results/family-gap-run-001'


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def canon(x): return json.dumps(x,sort_keys=True,separators=(',',':'))


def digest(x): return hashlib.sha256(canon(x).encode()).hexdigest()


def real(q): q=Q(q); return flint.arb(q.numerator)/q.denominator


def h(t,A): return sum((w*t/(v+(1-v)*t) for w,v in A),Q(0))


def equal_share(v,m):
    return abs(sum((Q((-1)**r*comb(m,r))*(1-Q(r,m))/(v+(1-v)*(1-Q(r,m))) for r in range(m+1)),Q(0)))


def sparse(n,A):
    fs=factor(n); g=gcd(*fs.values()); ps=list(fs); result=flint.arb(0)
    for k in divisors(g):
        if not mu(k): continue
        ln=sum((real(Q(e,k))*flint.arb(p).log() for p,e in fs.items()),flint.arb(0)); row=flint.arb(0)
        for bits in product((0,1),repeat=len(ps)):
            t=1-sum((flint.arb(p).log() for p,b in zip(ps,bits) if b),flint.arb(0))/ln
            row+=(-1)**sum(bits)*sum((real(w)*t/(real(v)+real(1-v)*t) for w,v in A),flint.arb(0))
        result+=real(Q(mu(k),k))*row
    return result


def main():
    flint.ctx.prec=512
    sourcepath=DEST/'family_gap_search.json'; source=json.loads(sourcepath.read_text())
    protocol=json.loads((DEST/'protocol.json').read_text()); batch=json.loads((DEST/'candidate_batch.json').read_text())
    assert source['protocol']==protocol and batch['protocol_sha256']==digest(protocol)
    assert source['fingerprint']['candidate_batch_sha256']==digest(batch)
    assert protocol['search_code_sha256']==sha(BASE/'compensated_gap_family_search.py')
    assert protocol['polynomial_backend_code_sha256']==sha(BASE/'compensated_global_gap_probe.py')
    assert protocol['counterexample_backend_code_sha256']==sha(BASE/'check_shift_ratio.py')
    assert protocol['source_sha256']==sha(BASE/'compensated-shift-results/compensated_shift_search.json')
    assert source['fingerprint']['protocol_sha256']==digest(protocol)
    old=json.loads((BASE/'compensated-shift-results/compensated_shift_verification.json').read_text())
    assert old['all_passed'] and old['source_artifact_sha256']==protocol['source_sha256']
    assert old['checker_code_sha256']==sha(BASE/'check_compensated_shift.py')
    original=json.loads((BASE/'compensated-shift-results/compensated_shift_search.json').read_text())
    assert len(batch['candidates'])==len(source['records'])==len(original['pair_compensators'])
    signatures={(r['left'],r['right']):r for r in old['all_order_signature_audit']['records']}
    own_records=[]; polynomial_count=0; full_count=0; counter_count=0; numerical_count=0
    for row,candidate,parent in zip(source['records'],batch['candidates'],original['pair_compensators']):
        assert row['candidate']==candidate
        assert (candidate['left'],candidate['right'])==(parent['left'],parent['right'])
        assert candidate['proposed_gap']==parent['fitted_global_gap']
        assert candidate['finite_peak_index']==parent['maximum_index']
        signature=signatures[candidate['left'],candidate['right']]
        assert signature['all_integer_orders_decided_by_valuations']
        assert candidate['ordinary_zero_all_order_gate']==(signature['possible_canceled_leading_order'] is None)
        A=[(Q(w),Q(v)) for w,v in candidate['atoms']]; gamma=Q(candidate['proposed_gap'])
        u,v=Q(candidate['left']),Q(candidate['right']); aa,bb=1/u-u,1/v-v
        assert A==[(-bb/(aa-bb),u),(aa/(aa-bb),v)]
        assert 0<u<v<1 and sum(w for w,v in A)==1 and gamma>0
        bu,bv=(1-u)**2/u,(1-v)**2/v
        K=aa*bb*(bu-bv)/(aa-bb)
        assert gamma==K*Q(1,16)/((1+bu/4)*(1+bv/4))
        if row['status']=='counterexample_found':
            n=int(row['counterexample_index']); assert n>=4 and sum(factor(n).values())>=2
            value=sparse(n,A); assert value.abs_lower()>real(gamma)
            if 'counterexample_ball' in row: assert value.overlaps(flint.arb(row['counterexample_ball']))
            assert not row['all_scale_bound_proved']; counter_count+=1
            own_records.append({'left':str(u),'right':str(v),'status':'counterexample_found','index':str(n),'all_passed':True}); continue
        A1=max(abs(w)*(1-v) for w,v in A); G1=int(A1//gamma)+1; assert G1>=2
        m0=next(m for m in range(3,protocol['resources']['maximum_factor_tail_search']+1) if max(abs(w)*equal_share(v,m) for w,v in A)<gamma)
        assert m0==row['factor_count_tail']
        expected_tails=[{'omega':1,'g_at_least':G1,'bound':str(A1/G1)},
                        {'omega_at_least':m0,'g_at_least':1,'bound':str(max(abs(w)*equal_share(v,m0) for w,v in A))}]
        expected_regions=[]
        for m in range(2,m0):
            Am=max(abs(w)*equal_share(v,m) for w,v in A); Gm=int(Am//gamma)+1
            expected_tails.append({'omega':m,'g_at_least':Gm,'bound':str(Am/Gm)})
            for g in range(1,Gm):
                if m==2 and g==1: expected_regions.append((m,g,False,'exact_two_prime_pair_certificate'))
                expected_regions.append((m,g,m==2 and g==1,None))
        assert expected_tails==row['uniform_tails'] and all(Q(r['bound'])<gamma for r in expected_tails)
        assert [r['exponent'] for r in row['prime_power_regions']]==list(range(2,G1))
        for r in row['prime_power_regions']:
            e=r['exponent']; value=sum((Q(mu(k),k)*(1-h(1-Q(k,e),A)) for k in divisors(e)),Q(0))
            assert value==Q(r['coefficient']) and abs(value)<=gamma
        regions=row['finite_simplex_regions']
        assert [(r['omega'],r['g'],r['repeated_exponent']) for r in regions]==[(m,g,b) for m,g,b,_ in expected_regions]
        complete=True
        for r in regions:
            if r['status']=='exact_two_prime_pair_certificate':
                assert r['omega']==2 and r['g']==1 and not r['repeated_exponent']; continue
            if r['status']!='universal_simplex_bound_certified': complete=False
            if 'sides' not in r:
                assert r['status']=='unsupported_by_resource_budget'; continue
            H,D,T,positive=homogeneous(r['omega'],r['g'],A,r['repeated_exponent'])
            assert r['denominator_degree']==max(sum(a) for a in D)
            assert positive>0
            all_sides=True
            assert len(r['sides'])==2 and {s['sign'] for s in r['sides']}=={-1,1}
            for s in r['sides']:
                cert=s['certificate']; P=add(scale(D,gamma),H,Q(s['sign']))
                own=primitive(P); supplied={tuple(m):int(c) for m,c in cert['primitive_initial_integer_coefficients']}
                assert own==supplied
                if cert['status']!='universal_nonnegative_polynomial_certified': all_sides=False; continue
                assert isinstance(cert['elevation'],int) and 0<=cert['elevation']<=protocol['resources']['maximum_polya_elevations']
                for _ in range(cert['elevation']): own=mul(own,T)
                assert all(c>=0 for c in own.values()) and len(own)==cert['final_coefficient_count']
                assert str(min(own.values()))==cert['minimum_nonzero_integer_coefficient']; polynomial_count+=1
            assert (r['status']=='universal_simplex_bound_certified')==all_sides
        assert row['all_scale_bound_proved']==complete
        assert row['status']==('universal_arithmetic_theorem_proved' if complete else 'numerical_lead')
        if complete: full_count+=1
        else: numerical_count+=1
        own_records.append({'left':str(u),'right':str(v),'gap':str(gamma),'status':row['status'],
                            'complete_integer_partition_checked':True,'all_passed':True})
        print('Independent family gap',str(u),str(v),row['status'],flush=True)
    assert source['status_counts']==dict(Counter(r['status'] for r in source['records']))
    proved=[r for r in source['records'] if r['all_scale_bound_proved'] and r['candidate']['ordinary_zero_all_order_gate']]
    expected=min(proved,key=lambda r:Q(r['candidate']['proposed_gap'])) if proved else None
    assert source['selected_operator']==expected and source['all_scale_verified_candidates']==len(proved)
    checks={'frozen_protocol_candidate_batch_source_and_backend_integrity':True,
            'all_exact_simplex_polynomial_and_positive_denominator_certificates':True,
            'independent_equal_share_uniform_norms_and_unbounded_case_thresholds':True,
            'all_prime_power_cases_and_complete_residual_integer_partitions':True,
            'rigorous_actual_integer_counterexamples_and_unproved_leads_retained':True,
            'automatic_selection_and_separate_zero_order_novelty_RH_gates':True}
    out={'all_passed':True,'checks':checks,'records':own_records,'proved_global_gap_estimates':full_count,
         'rigorous_counterexamples':counter_count,'numerical_leads_retained':numerical_count,
         'independent_polynomial_certificates_checked':polynomial_count,
         'selected_parameters':None if expected is None else {'left':expected['candidate']['left'],'right':expected['candidate']['right'],'gap':expected['candidate']['proposed_gap']},
         'source_artifact_sha256':sha(sourcepath),'checker_code_sha256':sha(Path(__file__)),
         'independent_polynomial_backend_code_sha256':sha(BASE/'check_compensated_global_gap.py'),
         'proof_sha256':sha(BASE/'compensated_family_gap_proof.txt'),
         'mathematical_audit_imports_production_code':False,'historical_novelty_established':False,'verified_new_operators':[]}
    (DEST/'family_gap_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent family certificate audit',full_count,'global bounds',counter_count,'counterexamples',numerical_count,'numerical leads',flush=True)


if __name__=='__main__': main()
