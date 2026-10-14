"""Postrun proof feedback: exclude storage formulas with known bulk growth.

The analytical rules are supplied by the two named reviews. This checker
substitutes exact candidate coefficients; unknown modes remain unknown.
It neither reads finite data nor modifies a frozen search result.
"""
from fractions import Fraction as Q
from math import factorial


PROFILE = [['8','10','1'],['16','20','-1']]
BASE_LABELS = ['Z','unit','omega1','omega2','omega3','omega_ge4']


def parse(value):
    if type(value) is not str:
        raise ValueError('canonical rational strings required')
    result = Q(value)
    if str(result) != value or max(result.numerator.bit_length(), result.denominator.bit_length()) > 4096:
        raise ValueError('canonical bounded rational required')
    return result


def analyze(candidate):
    if candidate['schema'] != 'signed-prime-storage-candidate-v1' or candidate['spec']['profile'] != PROFILE:
        raise ValueError('registered theorem is for the complete072/073 source profile')
    theta = list(map(parse,candidate['spec']['theta']))
    if theta != sorted(set(theta)) or any(not 0<t<1 for t in theta):
        raise ValueError('fixed finite list of distinct rational smooth cutoffs')
    if candidate['labels'] != BASE_LABELS+['smooth:'+str(t) for t in theta]:
        raise ValueError('complete source coordinate binding')
    q = parse(candidate['q'])
    if not 1<=q<=2:
        raise ValueError('admitted normalization exponent')
    results = []
    for index,ray in enumerate(candidate['rays']):
        weight = parse(ray['weight'])
        direction = list(map(parse,ray['direction']))
        if weight<=0 or len(direction)!=len(candidate['labels']):
            raise ValueError('positive complete square direction')
        differences = [direction[r+1]-direction[5] for r in (1,2,3)]
        record = dict(ray=index,weight=str(weight),effective_target_coefficient=str(direction[0]+direction[5]),
                      effective_smooth_direction=[str(v) for v in direction[6:]],
                      all_finite_drift_constants_excluded=False)
        if q==2:
            record['status']='NORMALIZATION_OUTSIDE_POSITIVE_POWER_OBSTRUCTION'
        elif any(differences):
            r=max(r for r in (1,2,3) if differences[r-1])
            leading=Q(2*(-1)**(r+1),factorial(r-1))*differences[r-1]
            record.update(status='FIXED_FACTOR_COUNT_BULK',leading_coefficient=str(leading),
                          log_denominator_power=2,loglog_numerator_power=2*(r-1),
                          theorem='MOBIUS_PRIME_STORAGE_ASYMPTOTIC_REVIEW_073.txt')
        elif any(v and t<=Q(1,2) for v,t in zip(direction[6:],theta)):
            record['status']='UNREGISTERED_LOW_CUTOFF_SECOND_ORDER_MODE'
        else:
            leading=2*sum(direction[6:],Q(0))
            if leading:
                record.update(status='SECOND_ORDER_SMOOTH_BULK',leading_coefficient=str(leading),
                              log_denominator_power=4,loglog_numerator_power=0,
                              theorem='MOBIUS_PRIME_STORAGE_CANDIDATE_REVIEW_073.txt')
            else:
                record['status']='REGISTERED_LEADING_MODES_CANCELLED_FURTHER_CONTROL_OPEN'
        if 'leading_coefficient' in record:
            leading=Q(record['leading_coefficient'])
            record.update(all_finite_drift_constants_excluded=True,
                          positive_power=str(2-q),liminf_energy_coefficient=str(weight*leading**2),
                          any_finite_base_extension_excluded=True)
        results.append(record)
    excluded=[r for r in results if r['all_finite_drift_constants_excluded']]
    return dict(schema='signed-prime-storage-asymptotic-feedback-v1',q=str(q),rays=results,
                status='REFUTED_FOR_EVERY_FINITE_DRIFT_CONSTANT' if excluded else 'NO_EXCLUSION_BY_REGISTERED_MODES',
                excluding_rays=[r['ray'] for r in excluded],
                current_source='N15k,y16k,p3,q5,r1,j1; necessary family only',
                analytic_rules_supplied=True,numerical_values_accessed=False,
                proof_scope='candidate auxiliary growth; no lower bound for actual signed Z',
                uniform_recurrence_proved=False,uniform_head_bound_proved=False,RH_proved=False)
