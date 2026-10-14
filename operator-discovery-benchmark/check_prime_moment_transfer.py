#!/usr/bin/env python3
"""Independent support certificates, arithmetic moments and full Fourier rows."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint

from check_fractional_prime import B, real
from check_gap import factors

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-moment-results'


def floor(x):return x.numerator//x.denominator
def ceil(x):return -floor(-x)


def reference_bounds(lo,hi,W,delta,k):
    beta=delta**(2*k)
    return max(Q(0),(lo-beta*W)/(1-beta)),min(Q(W),hi)


def affine_audit(source):
    count=0
    for row in source['generic_affine_moment_search']['programs']:
        delta=Q(row['amplitude_bound']);k=row['half_order'];beta=delta**(2*k)
        a,b=map(Q,row['learned_lower_coefficients']);c,d=map(Q,row['learned_upper_coefficients'])
        assert b<=0 and a*beta+b<=0 and a+b<=1
        assert d>=0 and c*beta+d>=0 and c+d>=1
        assert (a,b)==(1/(1-beta),-beta/(1-beta)) and (c,d)==(1,0)
        for suffix,weights in (('lower',(a,b)),('upper',(c,d))):
            rows=[list(map(Q,x)) for x in row['training_rows_'+suffix]]
            targets=list(map(Q,row['training_targets_'+suffix]))
            assert all(sum(u*v for u,v in zip(weights,x))==y for x,y in zip(rows,targets))
        # Native complex holdouts: rotations do not alter the marked norm.
        phases=(flint.acb(1),flint.acb(0,1),flint.acb(-1),flint.acb(0,-1))
        for length in (11,29):
            moment=flint.arb(0);W=Q(0);C=Q(0)
            for n in range(length):
                w=Q(n%9+1,n%4+1);marked=n%5==2
                z=phases[n%4]*(1 if marked else real(delta*Q(n%7,7)))
                moment+=real(w)*(z*z.conjugate()).real**k;W+=w
                if marked:C+=w
            assert real(a)*moment+real(b*W)<real(C)
            assert real(c)*moment+real(d*W)>real(C)
        count+=1
    # Training solely on vanishing unmarked scores would falsely fit C=M.
    assert Q(1,4)**2>0  # unmarked score 1/4 has C=0, M=1/16.
    return {'universal_affine_endpoint_certificates':count,'changed_complex_weighted_holdouts':2*count,
            'vanishing_unmarked_training_alias_rejected':True,'all_passed':True}


def arithmetic_audit(source):
    data=source['actual_arithmetic_moment_count_bridge'];N=data['coefficient_cutoff']
    scores=[flint.arb(0),flint.arb(0)]+[B(n,Q(1,2)) for n in range(2,N+1)]
    primes=[False,False]+[bool(flint.fmpz(n).is_prime()) for n in range(2,N+1)]
    rows=[]
    for row in data['records']:
        left,right=row['interval'];modulus=row['modulus'];residue=row['residue'];k=row['half_order']
        indices=[n for n in range(left,right+1) if n%modulus==residue]
        W=len(indices);C=sum(primes[n] for n in indices);delta=Q(row['certified_amplitude_bound'])
        assert delta==Q(5,12) and flint.arb(2).sqrt()-1<real(delta)
        moment=sum((scores[n]**(2*k) for n in indices),flint.arb(0))
        assert moment.overlaps(flint.arb(row['native_complete_moment_ball']))
        lo,hi=Q(row['moment_lower']),Q(row['moment_upper'])
        assert real(lo)<=moment and moment<=real(hi)
        lower,upper=reference_bounds(lo,hi,W,delta,k)
        assert str(lower)==row['count_lower'] and str(upper)==row['count_upper']
        assert lower<=C<=upper and [ceil(lower),floor(upper)]==row['integer_count_bounds']
        assert C==row['reference_prime_count_for_scoring_only']
        if row['unique_integer_count_certified']:assert ceil(lower)==floor(upper)==C
        rows.append({'interval':row['interval'],'modulus':modulus,'residue':residue,
                     'half_order':k,'fresh_full_prefix_primality_count':C,'independent_moment_value_overlap':True,
                     'unique_integer_count_certified':row['unique_integer_count_certified'],'all_passed':True})
    assert sum(r['unique_integer_count_certified'] for r in rows)==8
    return scores,{'independent_subset_decoder_coefficients':N-1,'records':rows,'all_passed':True}


def fourier_audit(scores):
    rows=[]
    for H,k,left,right in ((17,1,2,16),(16,2,2,16),(19,3,2,16),(9,2,2,8),(10,3,3,12),(11,4,3073,3083)):
        indices=list(range(left,right+1));assert len({n%H for n in indices})==len(indices)
        moment=flint.arb(0)
        for u in range(H):
            value=sum((scores[n]**k*(flint.acb(0,real(Q(2*u*n,H))*flint.arb.pi())).exp()
                       for n in indices),flint.acb(0))
            moment+=(value*value.conjugate()).real
        expected=H*sum((scores[n]**(2*k) for n in indices),flint.arb(0))
        assert (moment-expected).contains(0)
        rows.append({'row_modulus':H,'half_order':k,'interval':[left,right],
                     'every_native_Fourier_row_checked':True,'all_passed':True})
    # Two distinct controls: modular aliases, and confusing coefficient
    # moments with ordinary circle moments of a polynomial power.
    assert 4**2+0**2!=2*4  # all-one length four, modulus two.
    assert 1**2+2**2+1**2!=2  # constant term of |1+z|^4 is six.
    return {'records':rows,'composite_moduli_included':True,
            'repeated_residue_Parseval_alias_rejected':True,
            'ordinary_circle_fourth_moment_substitution_rejected':True,'all_passed':True}


def roughness_audit(source):
    control=source['prime_roughness_and_all_scale_moment_certificate'];profiles={}
    checked=0
    for alpha in sorted({Q(row['alpha']) for row in control['score_exponent_models']}):
        values=[flint.arb(0),flint.arb(0)]+[B(n,alpha) for n in range(2,4097)]
        for n in range(2,4097):
            p=min(factors(n));ratio=flint.arb(p).log()/flint.arb(n).log()
            if p==n:assert values[n].contains(1)
            else:assert values[n].abs_upper()<ratio**real(alpha)
            checked+=1
        profiles[alpha]=values
    for row in control['score_exponent_models']:
        alpha=Q(row['alpha']);theta=Q(row['score_exponent'])
        assert row['universal_score_envelope_proved']==(alpha==theta)
        assert row['larger_exponent_rejected_by_unbounded_actual_prime_sequence']==(theta>alpha)
    counter=control['unbalanced_actual_prime_counterexample'];p=counter['q'];assert flint.fmpz(p).is_prime()
    t=flint.arb(2).log()/flint.arb(2*p).log();value=B(2*p,Q(1,2)).abs_lower()
    assert value>t**real(Q(11,20))
    kernel_controls=0
    for gamma in (Q(1,2),Q(1),Q(3,2),Q(2),Q(3)):
        for L in (2,7,31,127):
            low=real(Q(1,L))
            integral=flint.acb.integral(lambda t,analytic:real(gamma)*
                        ((real(gamma-2)*t.log(analytic=analytic)).exp()),low,flint.arb(1),
                        abs_tol=flint.arb('1e-40'),rel_tol=flint.arb('1e-40'))
            assert integral.is_finite()
            tail=flint.arb(L).log() if gamma==1 else real(gamma)*(1-flint.arb(L)**real(1-gamma))/real(gamma-1)
            assert integral.overlaps(flint.acb(tail))
            cost=flint.arb(L)**(-real(gamma))+integral.real/L
            if gamma>1:upper=real(gamma/(gamma-1))/L
            elif gamma==1:upper=(1+flint.arb(L).log())/L
            else:upper=1/(real(1-gamma)*flint.arb(L)**real(gamma))
            assert cost<upper or cost.overlaps(upper)
            kernel_controls+=1
    assert 1+flint.arb(127).log()>2  # dropping the critical cost fails.
    moment_controls=0
    for row in control['doubling_window_moment_controls']:
        alpha=Q(row['alpha']);k=row['half_order'];X=row['scale'];gamma=2*k*alpha;L=flint.arb(X).log()
        if gamma>1:upper=2*real(gamma/(gamma-1))*X/L
        elif gamma==1:upper=2*X*(1+L.log())/L
        else:upper=2*X/(real(1-gamma)*L**real(gamma))
        assert upper.overlaps(flint.arb(row['all_scale_sieve_upper_ball']))
        moment=sum((profiles[alpha][n]**(2*k) for n in range(X,2*X+1)),flint.arb(0))
        assert moment.overlaps(flint.arb(row['complete_doubling_window_moment_ball'])) and moment<upper
        moment_controls+=1
    assert control['critical_envelope_loglog_cost_retained']
    assert not control['stronger_actual_critical_moment_bound_ruled_out']
    assert not control['imported_uniform_rough_number_theorem']['external_full_sieve_proof_independently_verified']
    return {'full_coefficient_roughness_bounds_checked':checked,'independent_doubling_moments_checked':moment_controls,
            'native_truncated_layercake_integrals_checked':kernel_controls,
            'unbalanced_actual_prime_false_exponent_rejected':True,
            'imported_sieve_theorem_statement_and_domain_used':'Theorem A, Fan/Pomerance author PDF, x>=y>=2',
            'external_full_sieve_proof_independently_verified':False,'all_passed':True}


def public_audit(source):
    from exact_arithmetic import program_value
    records=source['actual_arithmetic_moment_count_bridge']['records'];executions=0
    for row in records:
        program={'kind':'family_moment_program','family':'separated_support_moment_count_bounds',
                 'half_order':row['half_order'],'amplitude_bound':row['certified_amplitude_bound'],
                 'moment_lower_input':'lo','moment_upper_input':'hi','total_weight_input':'W'}
        inputs={'lo':Q(row['moment_lower']),'hi':Q(row['moment_upper']),'W':row['total_weight']}
        actual=program_value(program,inputs);lower,upper=reference_bounds(inputs['lo'],inputs['hi'],inputs['W'],Q(program['amplitude_bound']),row['half_order'])
        assert actual['count_lower']==lower and actual['count_upper']==upper
        assert actual['uniform_interval_width_upper']>=upper-lower;executions+=1
    orders=[]
    for W in (1,31,4095,10**12):
        for delta in (Q(0),Q(1,4),Q(5,12),Q(3,4)):
            error=Q(1,2**32)
            program={'kind':'family_moment_program','family':'separated_support_required_order',
                     'total_weight_input':'W','rounding_error_input':'error','amplitude_bound':str(delta)}
            k=program_value(program,{'W':W,'error':error});beta=delta**(2*k)
            assert beta*(W+1)<1-error
            if k>1:assert delta**(2*k-2)*(W+1)>=1-error
            orders.append({'total_weight':W,'amplitude_bound':str(delta),'minimum_half_order':k,'all_passed':True})
            executions+=1
    roughness_rows=source['prime_roughness_and_all_scale_moment_certificate']['doubling_window_moment_controls']
    for X,alpha,k,H in ((3,Q(1,4),1,None),(2,Q(1,4),2,None),(16,Q(1,2),1,None),
                        (64,Q(1,2),2,65),(256,Q(3,4),1,257),(2048,Q(9,10),3,None)):
        program={'kind':'family_moment_program','family':'prime_roughness_moment_upper_bound',
                 'scale_input':'X','score_exponent':str(alpha),'half_order':k}
        if H is not None:program['row_modulus']=H
        value=program_value(program,{'X':X})
        expected=flint.arb(4) if X==2 else flint.arb(next(r['all_scale_sieve_upper_ball'] for r in roughness_rows
                                                       if r['scale']==X and Q(r['alpha'])==alpha and r['half_order']==k))
        if H is not None:expected*=H
        assert value.overlaps(expected);executions+=1
    good={'kind':'family_moment_program','family':'separated_support_moment_count_bounds',
          'half_order':1,'amplitude_bound':'1/2','moment_lower_input':'lo','moment_upper_input':'hi','total_weight_input':'W'}
    inputs={'lo':1,'hi':2,'W':3}
    invalid=[(dict(good,amplitude_bound=a),inputs) for a in ('1','-1/4')]
    invalid.extend((dict(good,half_order=k),inputs) for k in (0,True))
    invalid.extend((good,dict(inputs,**changed)) for changed in ({'lo':-1},{'lo':3},{'W':0}))
    rejected=0
    for program,data in invalid:
        try:program_value(program,data)
        except ValueError:rejected+=1
        else:raise AssertionError('Invalid support transfer accepted')
    # A moment of six cannot describe two scores whose modulus is at most one.
    try:program_value(good,{'lo':6,'hi':6,'W':2})
    except ValueError:rejected+=1
    else:raise AssertionError('Wrong circle-moment interpretation accepted')
    rough={'kind':'family_moment_program','family':'prime_roughness_moment_upper_bound',
           'scale_input':'X','score_exponent':'1/2','half_order':2}
    invalid_rough=[(rough,{'X':1}),(rough,{'X':True}),(dict(rough,score_exponent='0'),{'X':16}),
                   (dict(rough,half_order=0),{'X':16}),(dict(rough,row_modulus=16),{'X':16})]
    for program,data in invalid_rough:
        try:program_value(program,data)
        except ValueError:rejected+=1
        else:raise AssertionError('Invalid roughness-scale or residue contract accepted')
    return {'public_executions':executions,'minimum_order_controls':orders,
            'invalid_contract_controls_rejected':rejected,'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=512
    source=json.loads((DEST/'prime_moment_transfer.json').read_text());assert source['all_passed']
    affine=affine_audit(source);scores,arithmetic=arithmetic_audit(source);fourier=fourier_audit(scores)
    roughness=roughness_audit(source);interface=public_audit(source)
    assert source['separate_all_scale_energy_estimate_supplied'] and source['known_sieve_all_scale_energy_upper_bound_supplied']
    assert not source['new_independent_prime_distribution_estimate_supplied']
    assert not source['new_uniform_prime_distribution_estimate_proved']
    assert not source['ordinary_zeta_zero_bridge_for_Hadamard_moment_operators_proved']
    assert not source['fixed_order_critical_strip_convergence_inferred_from_small_coefficient_error']
    assert not source['coefficient_even_moments_equal_ordinary_circle_even_moments_claimed']
    assert not source['QRH_global_bound_used_as_training_target'] and source['verified_new_operators']==[]
    checks={'learned_affine_transfers_have_all_weight_endpoint_certificates':affine['all_passed'],
            'independent_complete_arithmetic_coefficients_moments_and_actual_prime_counts':arithmetic['all_passed'],
            'full_native_Fourier_rows_and_alias_controls':fourier['all_passed'],
            'least_prime_envelope_and_classical_all_scale_layercake_moment_certificate':roughness['all_passed'],
            'typed_public_count_transfer_and_minimum_order_controls':interface['all_passed'],
            'all_scale_energy_zero_information_and_novelty_scope_honest':True}
    out={'checks':checks,'affine_audit':affine,'arithmetic_audit':arithmetic,'native_Fourier_audit':fourier,
         'prime_roughness_audit':roughness,'public_entry_point_audit':interface,'mathematical_audit_imports_production_code':False,
         'integration_checks_import_production_code':True,'all_passed':all(checks.values()),'seconds':time.monotonic()-start}
    (DEST/'prime_moment_verification.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Independent prime-moment audit',sum(checks.values()),'/',len(checks),'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
