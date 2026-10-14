"""Export exact prime-dilation leaves without claiming their signed bounds."""
from fractions import Fraction as Q

from check_mobius_centered_storage_074 import verify_grammar


def disposition(candidate_result, final_result):
    last = candidate_result['history'][-1]
    final = final_result['learned']
    if last['adaptation_violations'] or last['adaptation_status'] == 'REFUTED':
        status = 'REFUTED_ON_KNOWN_ADAPTATION_DOMAIN'
    elif final['status'] == 'REFUTED':
        status = 'REFUTED_ON_FINAL_DOMAIN'
    elif last['adaptation_status'] != 'VERIFIED_ON_FINITE_DOMAIN' or final['status'] != 'VERIFIED_ON_FINITE_DOMAIN':
        status = 'FINITE_EVIDENCE_UNRESOLVED'
    else:
        status = 'FINITE_SURVIVOR_REQUIRES_ANALYTICAL_PROOF'
    return dict(status=status, final_domain_status=final['status'],
                adaptation_violations=last['adaptation_violations'],
                final_violations=len(final['violating_scales']),
                promoted_to_uniform_bound=False, uniform_recurrence_proved=False, RH_proved=False)


def export(candidate, branch):
    admission = verify_grammar(candidate, branch)
    if not admission['verified']:
        raise ValueError('independent grammar admission required: '+str(admission))
    theta = list(map(Q, candidate['spec']['theta']))
    rays = []
    for index, ray in enumerate(candidate['rays']):
        v = list(map(Q, ray['direction']))
        active = [(t,c) for t,c in zip(theta,v[6:]) if c]
        record = dict(ray=index, weight=ray['weight'], original_direction=ray['direction'],
                      target_coefficient=str(v[0]+v[5]), bound_proved=False)
        if any(t<Q(1,2) for t,c in active):
            record.update(status='UNREGISTERED_LOW_CUTOFF_CORRELATION',
                          smooth_terms=[dict(theta=str(t),coefficient=str(c)) for t,c in active],
                          unresolved='retain original signed smooth combination; unique-large-prime rule not applicable')
        else:
            if sum((c for t,c in active),Q(0)):
                raise ArithmeticError('registered bulk not annihilated')
            blocks=[];running=Q(0)
            for (lo,c),(hi,_) in zip(active,active[1:]):
                running+=c
                if running:
                    blocks.append(dict(lower_theta=str(lo),upper_theta=str(hi),
                                       coefficient=str(running),lower_endpoint='strict',upper_endpoint='closed'))
            record.update(status='EXACT_SIGNED_PRIME_DILATION_IDENTITY',prime_blocks=blocks,
                          identity='R(k)=a*Z(k)+sum_blocks b*sum_{(20k)^lo<p<=(20k)^hi, p prime} Z(k/p)',
                          qualitative_bound='O_A(k/log(k)^A) for every fixed A>0, constants depend on fixed coefficients and cutoffs',
                          qualitative_bound_is_RH_strength=False,
                          theorem='MOBIUS_CENTERED_STORAGE_REDUCTION_074.txt')
        rays.append(record)
    return dict(schema='signed-prime-dilation-obligation-v1',branch=branch,q=candidate['q'],
                source=candidate['spec'],rays=rays,
                source_stencil='Z(t)=M(10t)-M(8t)-M(20t)+M(16t)',
                M_definition='M(u)=sum_{1<=n<=floor(u)} mu(n), including the unit; M(u)=0 for 0<=u<1',
                identity_domain='integer k>=1; prime-dilated arguments k/p are positive rationals',
                integer_drift_does_not_control_rational_arguments=True,
                target_square='Z(k)^2',
                energy='E(k)=Z(k)^2+sum_rays weight*R_ray(k)^2',
                unpaid='uniform signed quadratic drift with all prime/composite cross terms and rational-scale transfers',
                no_absolute_values_inserted_in_identity=True,
                supplied_identity_rule_applied_to_learned_coefficients=True,
                uniform_recurrence_proved=False,uniform_head_bound_proved=False,RH_proved=False)
