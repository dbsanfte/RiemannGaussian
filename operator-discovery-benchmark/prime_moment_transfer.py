#!/usr/bin/env python3
"""Learn generic moment/count transfers, then instantiate actual zeta scores."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

import flint

from exact_arithmetic import program_value
from global_moment_grammar import separated_support_count_bounds, separated_support_required_order, roughness_moment_upper_bound
from global_moment_search import fit
from prime_scale_search import sieve

BASE=Path(__file__).resolve().parent
DEST=BASE/'prime-moment-results'


def endpoint_certificate(a,b,beta,lower):
    # Homogeneous affine bounds summed over arbitrary nonnegative weights.
    endpoints=(b,a*beta+b);marked=a+b
    return max(endpoints)<=0 and marked<=1 if lower else min(endpoints)>=0 and marked>=1


def learn_transfers():
    rows=[]
    for delta in (Q(1,4),Q(1,2),Q(3,4)):
        for k in (1,2,3,4):
            beta=delta**(2*k)
            # Unknown a,b for a*M+b*W. Generic saturation cases, with no
            # prime or zeta coefficient and no QRH exponent in training.
            lower_rows=[(beta*W,Q(W)) for W in (1,3,7)]+[(Q(W),Q(W)) for W in (1,3,7)]
            lower_targets=[Q(0)]*3+[Q(W) for W in (1,3,7)]
            upper_rows=[(Q(0),Q(W)) for W in (1,3,7)]+[(Q(W),Q(W)) for W in (1,3,7)]
            upper_targets=lower_targets
            lower_a,lower_b=fit(lower_rows,lower_targets)
            upper_a,upper_b=fit(upper_rows,upper_targets)
            assert endpoint_certificate(lower_a,lower_b,beta,True)
            assert endpoint_certificate(upper_a,upper_b,beta,False)
            held=0
            for length in (7,19,43):
                # Changed score magnitudes and rational, nonuniform weights.
                energy=Q(0);W=Q(0);C=Q(0)
                for i in range(length):
                    weight=Q(i%7+1,i%5+1);marked=i%4==1
                    norm_square=Q(1) if marked else delta*delta*Q((i%5)**2,25)
                    energy+=weight*norm_square**k;W+=weight
                    if marked:C+=weight
                assert lower_a*energy+lower_b*W<=C<=upper_a*energy+upper_b*W
                held+=1
            rows.append({'amplitude_bound':str(delta),'half_order':k,
                         'learned_lower_coefficients':[str(lower_a),str(lower_b)],
                         'learned_upper_coefficients':[str(upper_a),str(upper_b)],
                         'training_rows_lower':[list(map(str,row)) for row in lower_rows],
                         'training_targets_lower':list(map(str,lower_targets)),
                         'training_rows_upper':[list(map(str,row)) for row in upper_rows],
                         'training_targets_upper':list(map(str,upper_targets)),
                         'all_weight_endpoint_certificate':True,'changed_input_holdout_families':held,'all_passed':True})
    beta=Q(1,4)
    assert not endpoint_certificate(Q(1),Q(0),beta,True)
    return {'training_features':['moment','total_weight'],'programs':rows,
            'zero_composite_training_alias_rejected':True,'prime_or_QRH_target_used_in_training':False,'all_passed':True}


def dyadic_enclosure(x,denominator=2**48):
    lo=(x.lower()*denominator).floor();hi=(x.upper()*denominator).ceil()
    assert lo.is_exact() and hi.is_exact()
    return max(Q(0),Q(int(lo.fmpz()),denominator)),Q(int(hi.fmpz()),denominator)


def arithmetic_cases():
    cutoff=4096
    scores=program_value({'kind':'fractional_prime_program','family':'fractional_prime_decoder',
                          'alpha':'1/2','input':'f'},{'f':[0]+[1]*cutoff})
    spf,_=sieve(cutoff);delta=Q(5,12)
    assert flint.arb(2).sqrt()-1<flint.arb(delta.numerator)/delta.denominator
    windows=[(2,D,1,0) for D in (16,64,256,1024,4096)]
    windows.extend(((3073,4096,1,0),(2,4096,3,1),(2,4096,7,3)))
    rows=[]
    for left,right,modulus,residue in windows:
        indices=[n for n in range(left,right+1) if n%modulus==residue]
        W=len(indices);reference_count=sum(spf[n]==n for n in indices)
        epsilon=Q(2,2**48);selected=separated_support_required_order(W,delta,epsilon)
        for k in sorted({1,selected}):
            moment=sum((scores[n]**(2*k) for n in indices),flint.arb(0))
            lo,hi=dyadic_enclosure(moment);assert hi-lo<=epsilon
            bounds=separated_support_count_bounds(lo,hi,W,delta,k)
            assert bounds['count_lower']<=reference_count<=bounds['count_upper']
            integer_lower=-((-bounds['count_lower'].numerator)//bounds['count_lower'].denominator)
            integer_upper=bounds['count_upper'].numerator//bounds['count_upper'].denominator
            unique=integer_lower==integer_upper
            if k==selected:assert unique and integer_lower==reference_count
            rows.append({'interval':[left,right],'modulus':modulus,'residue':residue,'total_weight':W,
                         'alpha':'1/2','certified_amplitude_bound':str(delta),'half_order':k,
                         'native_complete_moment_ball':moment.str(40),'moment_lower':str(lo),'moment_upper':str(hi),
                         'count_lower':str(bounds['count_lower']),'count_upper':str(bounds['count_upper']),
                         'integer_count_bounds':[integer_lower,integer_upper],
                         'unique_integer_count_certified':unique,'reference_prime_count_for_scoring_only':reference_count,
                         'selected_uniformly_sufficient_half_order':selected,'all_passed':True})
    return {'records':rows,'coefficient_cutoff':cutoff,'prime_labels_supplied_to_moment_program':False,
            'universal_coefficient_gap_proof':'fractional_prime_proof.txt section 3',
            'finite_energy_values_are_not_all_scale_energy_estimates':True,'all_passed':True}


def roughness_controls():
    source=json.loads((BASE/'fractional-prime-results/fractional_prime_search.json').read_text())
    cutoff=4096;spf,_=sieve(cutoff);models=[];moments=[]
    for profile in source['profiles']:
        alpha=Q(profile['alpha']);scores=list(map(flint.arb,profile['B_coefficients']))
        for excess in (Q(0),Q(1,20),Q(1,10),Q(1,4)):
            theta=alpha+excess;failures=[]
            for n in range(2,cutoff+1):
                if spf[n]==n:continue  # exact prime equality has its own proof
                ratio=flint.arb(spf[n]).log()/flint.arb(n).log()
                if not scores[n].abs_upper()<ratio**(flint.arb(theta.numerator)/theta.denominator):failures.append(n)
            models.append({'alpha':str(alpha),'score_exponent':str(theta),
                           'training_indices':[2,128],'held_out_indices':[129,cutoff],
                           'training_passed':not any(n<=128 for n in failures),'held_out_passed':not failures,
                           'first_finite_counterexample':next(iter(failures),None),
                           'universal_score_envelope_proved':not excess,
                           'larger_exponent_rejected_by_unbounded_actual_prime_sequence':bool(excess)})
        for k in (1,2,3):
            gamma=2*k*alpha
            for X in (3,16,64,256,1024,2048):
                moment=sum((scores[n]**(2*k) for n in range(X,2*X+1)),flint.arb(0))
                upper=roughness_moment_upper_bound(X,alpha,k)
                assert moment<upper
                moments.append({'alpha':str(alpha),'half_order':k,'scale':X,'gamma':str(gamma),
                                'regime':'density' if gamma>1 else 'critical_loglog' if gamma==1 else 'weaker_log_power',
                                'complete_doubling_window_moment_ball':moment.str(35),
                                'all_scale_sieve_upper_ball':upper.str(35),'all_passed':True})
    # A fit at exponent 11/20 survives every integer through 4096, but fails
    # at an actual squarefree coefficient using a fresh unbalanced prime pair.
    p=source['distant_prime_pair_controls']['records'][0]['p'];assert flint.fmpz(p).is_prime() and p>2
    l2,lp=flint.arb(2).log(),flint.arb(p).log();t=l2/(l2+lp)
    value=t.sqrt()+(1-t).sqrt()-1;false=t**(flint.arb(11)/20)
    assert value>false
    return {'score_exponent_models':models,'doubling_window_moment_controls':moments,
            'sharp_score_envelope':'|B_alpha(n)| <= (log P^-(n)/log n)^alpha for every n>=2',
            'unbalanced_actual_prime_counterexample':{'p':2,'q':p,'n':2*p,'alpha':'1/2','false_exponent':'11/20',
                                                      'coefficient_modulus_ball':value.str(35),
                                                      'false_upper_ball':false.str(35),'all_passed':True},
            'imported_uniform_rough_number_theorem':{'statement':'Phi(x,y)<x/log(y) for x>=y>=2; trivial extension to 1<y<2',
                                                    'source':'https://math.dartmouth.edu/~carlp/erat060523rev.pdf',
                                                    'location':'Theorem A, page 1','external_full_sieve_proof_independently_verified':False},
            'all_scale_density_bound':'For gamma=2*k*alpha>1, sum_(X<=n<=2X)|B_alpha(n)|^(2k) <= 2*gamma/(gamma-1)*X/log X, every integer X>=2',
            'half_order_fourth_moment_instance':'sum_(X<=n<=2X)|B_(1/2)(n)|^4 <= 4*X/log X',
            'critical_envelope_loglog_cost_retained':True,
            'stronger_actual_critical_moment_bound_ruled_out':False,
            'all_passed':True}


def main():
    start=time.monotonic();flint.ctx.prec=384
    learned=learn_transfers();arithmetic=arithmetic_cases();roughness=roughness_controls()
    out={'generic_affine_moment_search':learned,'actual_arithmetic_moment_count_bridge':arithmetic,
         'universal_count_transfer_proved':True,'universal_finite_order_selection_proved':True,
         'uniform_transfer':'(M_lo-delta^(2k)*W)/(1-delta^(2k)) <= marked_count <= M_hi, with nonnegative clipping',
         'prime_roughness_and_all_scale_moment_certificate':roughness,
         'separate_all_scale_energy_estimate_supplied':True,
         'all_scale_energy_estimate_domain':'Classical-sieve upper bounds for bounded nonnegative weights on [X,2X], with scale/order and residue-injectivity conditions',
         'new_independent_prime_distribution_estimate_supplied':False,
         'known_sieve_all_scale_energy_upper_bound_supplied':True,
         'complete_Fourier_second_moment_bridge':'sum_u |sum_n B(n)^k e_H(un)|^2 = H*sum_n |B(n)|^(2k) when support residues are distinct',
         'coefficient_even_moments_equal_ordinary_circle_even_moments_claimed':False,
         'new_uniform_prime_distribution_estimate_proved':False,
         'ordinary_zeta_zero_bridge_for_Hadamard_moment_operators_proved':False,
         'fixed_order_critical_strip_convergence_inferred_from_small_coefficient_error':False,
         'QRH_global_bound_used_as_training_target':False,
         'historical_novelty_established':False,'verified_new_operators':[],
         'proof':'prime_moment_transfer_proof.txt','all_passed':True,'seconds':time.monotonic()-start}
    DEST.mkdir(exist_ok=True);(DEST/'prime_moment_transfer.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Prime moment transfer',len(learned['programs']),'universal transfers',
          len(arithmetic['records']),'finite arithmetic groups; seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
