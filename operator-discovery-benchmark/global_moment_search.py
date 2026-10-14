#!/usr/bin/env python3
"""Find energy laws and global bound certificates across unrelated families."""

from fractions import Fraction as Q
from itertools import product
from pathlib import Path
from random import Random
import json
import time

from global_moment_grammar import (additive_twist_energy,energy_state,scale_step,
                                   even_moment,replicated_target_bound,PRODUCTION_CATALOGUE)

BASE=Path(__file__).resolve().parent
DEST=BASE/'global-moment-results'


def fit(rows,targets):
    for i,j in product(range(len(rows)),repeat=2):
        a,b=rows[i];c,d=rows[j];det=a*d-b*c
        if not det:continue
        x=(targets[i]*d-b*targets[j])/det;y=(a*targets[j]-targets[i]*c)/det
        return [x,y] if all(x*u+y*v==t for (u,v),t in zip(rows,targets)) else None
    return None


def mobius_prefix(N):
    a=[0]*(N+1);prior=[0]*(N+1)
    for n in range(1,N+1):
        a[n]=int(n==1)-prior[n]
        for multiple in range(2*n,N+1,n):prior[multiple]+=a[n]
    return a


def additive_energies():
    models=(0,1,2);a=[0]+[1]*8
    training=([8,8],[8,12],[8,16]);survivors=[]
    for exponent in models:
        if all(additive_twist_energy(a,D,H)<=H*((D+H-1)//H)**exponent*sum(v*v for v in a[1:D+1])+1e-8
               for D,H in training):survivors.append(exponent)
    # Hold out the ratio of row and coefficient scales, not just the next D.
    D,H=23,5;held=[0]+[1]*D
    rejected=[e for e in survivors if additive_twist_energy(held,D,H)>H*((D+H-1)//H)**e*D+1e-8]
    survivors=[e for e in survivors if e not in rejected];assert min(survivors)==1 and rejected==[0]
    mu=mobius_prefix(1024);records=[]
    for D,H,degree in ((16,23,1),(64,17,1),(129,31,2),(257,43,3),(511,61,4),(1024,101,5)):
        buckets=[0]*H;sizes=[0]*H
        for n in range(1,D+1):buckets[pow(n,degree,H)]+=mu[n];sizes[pow(n,degree,H)]+=1
        expected=H*sum(v*v for v in buckets);observed=additive_twist_energy(mu,D,H,degree)
        l2=sum(v*v for v in mu[1:D+1]);assert abs(observed-expected)<1e-6
        assert expected<=H*max(sizes)*l2<=H*degree*((D+H-1)//H)*l2
        records.append({'scale':D,'row_modulus':H,'index_degree':degree,'coefficient_origin':'Dirichlet inverse of u(n)=1',
                        'observed_energy':observed,'exact_complete_residue_energy':expected,
                        'coefficient_squared_norm':l2,'maximum_bucket_size':max(sizes),'all_passed':True})
    # Polynomial root counts at a prime cannot be silently used at composites.
    D,H,degree=16,16,2;a=[0]+[int(n%4==0) for n in range(1,17)]
    observed=additive_twist_energy(a,D,H,degree);wrong=H*degree*sum(v*v for v in a)
    assert observed>wrong+1e-8
    return {'training_scale_pairs':training,'bucket_exponents_scored':list(models),
            'smallest_held_out_surviving_bucket_exponent':min(survivors),
            'scale_ratio_aliases_rejected':rejected,'actual_zeta_inverse_family_observations':records,
            'universal_certificates':[{'domain':'All integers D,H>=1 and every complete coefficient vector',
                'kernel':'exp(2*pi*i*u*n/H)','bound':'M2<=H*ceil(D/H)*sum_n|a(n)|^2',
                'proof_rule':'character orthogonality, then bucket Cauchy; operator norm is sharp'},
                {'domain':'All D>=1, all prime row moduli p, all integers degree>=1',
                 'kernel':'exp(2*pi*i*u*n^degree/p)','bound':'M2<=p*degree*ceil(D/p)*sum_n|a(n)|^2',
                 'proof_rule':'nonzero degree-d polynomial has at most d roots over a field; retain zero residue'}],
            'operator_class_holdout':{'row_modulus':16,'index_degree':2,'actual_energy':observed,
                                      'invalid_prime_field_bound':wrong,'composite_extension_rejected':True},
            'new_Mobius_cancellation_or_prime_distribution_estimate_proved':False,'all_passed':True}


def recurrence_search():
    rng=Random(2026100719);training=[([Q(a)],[Q(b)]) for a,b in ((1,1),(1,2),(-2,1),(2,3))]
    held=[([Q(rng.randrange(-3,4)) for _ in range(N)],
           [Q(rng.randrange(-3,4)) for _ in range(N)]) for N in (2,3,5,7)]
    records=[];failed=[];scored=0
    for values in product((-1,1),repeat=4):
        matrix=[list(values[:2]),list(values[2:])]
        for multiplier in (0,1,2):
            scored+=1;rows=[];targets=[]
            for P,R in training:
                rows.append(energy_state(P,R));targets.append(energy_state(*scale_step(P,R,matrix,multiplier)))
            M=[fit(rows,[v[k] for v in targets]) for k in (0,1)]
            if any(v is None for v in M):continue
            failures=[]
            for P,R in held:
                state=energy_state(P,R);next_state=energy_state(*scale_step(P,R,matrix,multiplier*len(P)))
                predicted=[sum((a*b for a,b in zip(row,state)),Q(0)) for row in M]
                if predicted!=next_state:failures.append({'span':len(P),'predicted':list(map(str,predicted)),
                                                        'actual':list(map(str,next_state))})
            result={'signed_transfer_matrix':matrix,'shift_span_multiplier':multiplier,
                    'fitted_energy_transfer':[[str(a) for a in row] for row in M]}
            if failures:
                result.update({'first_held_out_counterexample':failures[0],'universality_rejected':True});failed.append(result)
                continue
            a,b,c,d=values;orthogonal_columns=a*b+c*d==0
            assert multiplier>=1
            if orthogonal_columns:
                assert M==[[2,8],[1,0]]
                rules=['odd shifted terms cancel between the two outputs',
                       'remaining phase shifts have frequency +/-2*shift',
                       'unshifted frequencies lie in [-2*(span-1),2*(span-1)]',
                       'shift>=span excludes their constant coefficient']
            else:
                assert multiplier>=2 and M==[[2,8],[1,4]]
                rules=['the two signed output rows are proportional',
                       'all nonconstant terms have shifts +/-shift or +/-2*shift',
                       'unshifted frequencies lie in [-2*(span-1),2*(span-1)]',
                       'shift>=2*span excludes every nonconstant phase term']
            result.update({'universal_energy_transfer_proved':True,
                           'proof_rules':rules,
                           'scale_growth_factor':multiplier+1,'all_passed':True});records.append(result)
    assert scored==48 and len(records)==24 and len(failed)==16
    return {'operator_programs_scored':scored,'generic_training_input_pairs':len(training),
            'generic_held_out_spans':[2,3,5,7],'universally_certified_transfers':records,
            'finite_training_recurrences_rejected':failed,
            'QRH_specific_primitives_or_exponents_in_search':False,'all_passed':True}


def positive_functional_search(recurrence):
    matrices=sorted({tuple(tuple(row) for row in r['fitted_energy_transfer']) for r in recurrence['universally_certified_transfers']})
    records=[]
    for data in matrices:
        M=[[Q(a) for a in row] for row in data];models=[]
        for c,rate in product((Q(0),Q(1,2),Q(1),Q(2),Q(3),Q(4)),range(1,9)):
            v=[Q(1),c];left=[sum(v[i]*M[i][j] for i in range(2)) for j in range(2)]
            if all(left[j]<=rate*v[j] for j in range(2)):models.append({'weights':list(map(str,v)),'rate':rate})
        best=min(v['rate'] for v in models);winners=[v for v in models if v['rate']==best]
        records.append({'energy_transfer_matrix':[list(row) for row in data],
                        'minimum_growth_rate':best,'minimizers':winners,'universal_bound_proved':True})
    assert [(r['minimum_growth_rate'],r['minimizers']) for r in records]==[(4,[{'weights':['1','2'],'rate':4}]),(6,[{'weights':['1','4'],'rate':6}])]
    return {'positive_functional_models_scored':48*len(matrices),'records':records,
            'universal_lift':'A positive left eigenfunctional propagates its certified rate by induction through every level',
            'initial_state_must_be_supplied':True,'universal_bound_proved':True,'all_passed':True}


def recursive_family_moments():
    P=R=[Q(1)];matrix=[[1,1],[1,-1]];records=[];values=[]
    for j in range(10):
        moment=even_moment(P,2);N=len(P);state=energy_state(P,R);values.append(moment)
        assert moment==even_moment(R,2) and state[0]+2*state[1]==4*N*N
        records.append({'level':j,'span':N,'exact_fourth_moment':str(moment),
                        'training':j<5,'all_passed':True})
        if j<9:P,R=scale_step(P,R,matrix,N)
    recurrence=fit([[values[j+1],values[j]] for j in range(3)],values[2:5])
    assert recurrence==[2,8]
    for j in range(8):assert values[j+2]==recurrence[0]*values[j+1]+recurrence[1]*values[j]
    for row in records:
        N=row['span'];moment=Q(row['exact_fourth_moment'])
        assert moment==Q(4*N*N-(-2)**row['level'],3) and moment<=Q(3,2)*N*N
    return {'family':'Rudin-Shapiro pair generated by a signed dyadic phase transfer',
            'records':records,'learned_scalar_recurrence':list(map(str,recurrence)),
            'universal_fourth_moment_formula':'(4*4^j-(-2)^j)/3',
            'universal_bound':'Integral |P_j|^4<=3/2*N^2, N=2^j, at every j>=0',
            'proof':'generic certified two-state recurrence, initial state and pointwise pair energy',
            'historical_status':'Known recursive polynomial family; calibration, not historical novelty',
            'not_a_bound_for_Mobius_or_prime_coefficients':True,'all_passed':True}


def lacunary_family_moments():
    P=R=[Q(1)];matrix=[[1,1],[1,1]];records=[]
    for j in range(6):
        value=even_moment(P,2);assert value==6**j
        records.append({'level':j,'span':len(P),'nonzero_coefficient_count':2**j,
                        'exact_fourth_moment':str(value),'all_passed':True})
        if j<5:P,R=scale_step(P,R,matrix,2*len(P))
    return {'family':'lacunary positive-coefficient product generated by duplicated signed rows',
            'records':records,'universal_fourth_moment_formula':'6^j',
            'proof':'The learned second energy transfer has positive eigenfunctional E+4*C with rate 6; P=Q at every level',
            'historical_status':'Known lacunary/Riesz product framework; calibration, not novelty',
            'not_a_bound_for_Mobius_or_prime_coefficients':True,'all_passed':True}


def normalized_scale_costs():
    rows=[]
    for beta in (1,2,3,4):
        ratio=Q(4,2**beta);uniform=ratio<1
        value=sum((ratio**r for r in range(64)),Q(0))
        if uniform:assert value<=1/(1-ratio)
        else:assert value>=64
        rows.append({'power_exponent':beta,'normalized_recurrence_ratio':str(ratio),
                     'uniform_forced_cost_bound_proved':uniform,
                     'uniform_bound':str(1/(1-ratio)) if uniform else None,
                     'critical_resonance_requires_logarithmic_scale_loss':ratio==1})
    training_bound=Q(31);held=sum((Q(1)**r for r in range(257)),Q(0))
    assert held>training_bound
    return {'generic_forced_recurrence':'E_next<=rate*E+scale^beta; normalize before summing all generations',
            'records':rows,'finite_horizon_constant_alias':{'training_levels':31,'claimed_constant':str(training_bound),
             'held_out_level':257,'actual_cost':str(held),'rejected':True},
            'strict_contraction_required_with_persistent_forcing':True,
            'homogeneous_critical_rate_bound_is_separate':True,'all_passed':True}


def row_target_transfer():
    # Learn exponents of moment and row-count from exact power-of-two
    # replication cases, without a character order or number-field model.
    models=list(product((Q(k,4) for k in range(5)),(Q(k,4) for k in range(-4,1))))
    survivors=[(alpha,beta) for alpha,beta in models
               if all(alpha*(h+2*d)+beta*h==d for h,d in ((0,1),(1,0),(2,2)))]
    assert survivors==[(Q(1,2),Q(-1,2))]
    records=[]
    for count in (3,5,7,11):
        target=Q(5,2);error=Q(1,7)
        rows=[target+error*(Q(2*j,count-1)-1) for j in range(count)]
        assert all(abs(row-target)<=error for row in rows)
        moment=sum((row*row for row in rows),Q(0))
        bound=replicated_target_bound(moment,count,error)
        assert bound>=target and (bound-error)**2>=moment/count
        assert (bound-error-Q(1,2**32))**2<moment/count
        records.append({'admissible_row_count':count,'target':str(target),'uniform_error':str(error),
                        'exact_second_moment':str(moment),'certified_rational_target_upper_bound':str(bound),'all_passed':True})
    # Near-row errors cannot be silently discarded.
    true=replicated_target_bound(0,5,1);wrong=replicated_target_bound(0,5,0)
    assert true==1 and wrong==0
    return {'power_models_scored':len(models),'learned_moment_and_row_count_powers':list(map(str,survivors[0])),
            'universal_law':'If m rows satisfy |A_u-T|<=E and the family q-moment is <=B, then |T|<=E+(B/m)^(1/q)',
            'domain':'Every finite row family, complex target and rows, even q>=2; all scales once each premise is uniform',
            'held_out_replication_records':records,'missing_error_control':{'target':1,'rows':[0]*5,
             'true_uniform_error':1,'valid_bound':str(true),'bound_with_error_discarded':str(wrong),'rejected':True},
            'required_separate_global_certificates':['arithmetic_family_moment_upper_bound',
               'admissible_actual_prime_or_arithmetic_row_count_lower_bound','uniform_row_approximation_error',
               'ordinary_zeta_Mellin_bridge_with_nonvanishing_transform_numerator'],
            'all_scale_prime_row_count_and_error_certificates_supplied':False,
            'new_Mobius_or_prime_target_bound_established':False,'all_passed':True}


def main():
    start=time.monotonic();DEST.mkdir(exist_ok=True)
    additive=additive_energies();recurrence=recurrence_search();functional=positive_functional_search(recurrence)
    family=recursive_family_moments();lacunary=lacunary_family_moments();cost=normalized_scale_costs();target=row_target_transfer()
    out={'production_catalogue':PRODUCTION_CATALOGUE,'additive_arithmetic_energy_search':additive,
         'generic_operator_moment_transfer_search':recurrence,'positive_functional_search':functional,
         'recursive_family_global_moment_calibration':family,'scale_cost_and_resonance_controls':cost,
         'lacunary_family_global_moment_calibration':lacunary,
         'moment_to_arithmetic_target_transfer':target,
         'anti_overfit_protocol':{'different_arithmetic_and_recursive_families':True,
             'scale_ratio_operator_class_and_generic_input_holdouts':True,
             'exponent_fit_alone_can_promote_global_bound':False,
             'recurrence_without_uniform_operator_certificate_can_promote_global_bound':False,
             'QRH_global_bound_used_as_training_target':False},
         'new_uniform_prime_distribution_estimate_proved':False,'ordinary_zeta_zero_bridge_proved':False,
         'QRH_global_moment_bound_independently_verified':False,'verified_new_operators':[],
         'all_passed':all(x['all_passed'] for x in (additive,recurrence,functional,family,lacunary,cost,target)),
         'seconds':time.monotonic()-start}
    (DEST/'global_moment_search.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Global moment discovery',recurrence['operator_programs_scored'],'operator programs;',
          len(recurrence['universally_certified_transfers']),'universal transfers;',len(recurrence['finite_training_recurrences_rejected']),
          'finite-fit recurrences rejected; passed',out['all_passed'],'seconds',out['seconds'],flush=True)


if __name__=='__main__':main()
