"""Discovery semantics for quantified energies and scale recurrences.

Exact finite evaluations are separate from the universal certificate. Circle
moments here have real rational coefficients and normalized Haar measure.
"""

from fractions import Fraction as Q
import numpy as np


def convolution(a,b):
    out=[Q(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=Q(x)*Q(y)
    return out


def even_moment(coefficients,power):
    if not isinstance(power,int) or power<1:raise ValueError('An even moment needs a positive integer half-order')
    if not coefficients:raise ValueError('A complete, nonempty coefficient vector is required')
    expanded=[Q(1)]
    for _ in range(power):expanded=convolution(expanded,coefficients)
    return sum((a*a for a in expanded),Q(0))


def energy_state(P,R):
    product=convolution(P,R)
    return [even_moment(P,2)+even_moment(R,2),sum((a*a for a in product),Q(0))]


def scale_step(P,R,matrix,shift):
    N=max(len(P),len(R))
    if not isinstance(shift,int) or shift<0:raise ValueError('Phase shift must be a nonnegative integer')
    if len(matrix)!=2 or any(len(row)!=2 for row in matrix):raise ValueError('A pair transfer requires a two-by-two matrix')
    outputs=[]
    for a,b in matrix:
        out=[Q(0)]*(N+shift)
        for n,x in enumerate(P):out[n]+=Q(a)*Q(x)
        for n,x in enumerate(R):out[n+shift]+=Q(b)*Q(x)
        outputs.append(out)
    return outputs


def additive_twist_energy(coefficients,D,H,index_degree=1):
    if not isinstance(D,int) or D<1 or not isinstance(H,int) or H<1:raise ValueError('Positive integer scale and row modulus are required')
    if len(coefficients)<=D:raise ValueError('Every coefficient through the declared scale is required')
    if not isinstance(index_degree,int) or index_degree<1:raise ValueError('Index degree must be a positive integer')
    n=np.array([pow(n,index_degree,H) for n in range(1,D+1)]);u=np.arange(H)
    kernel=np.exp(2j*np.pi*np.outer(u,n)/H)
    values=kernel@np.array([complex(a) for a in coefficients[1:D+1]])
    return float(np.vdot(values,values).real)


def replicated_target_bound(moment_upper,row_count,error,half_order=1,denominator=2**32):
    """Certified rational upper rounding of error+(moment/count)^(1/(2k)).

The caller must separately certify the moment, row count and approximation
premises. Evaluating this expression cannot establish those premises.
"""
    moment_upper=Q(moment_upper);error=Q(error)
    if moment_upper<0 or error<0:raise ValueError('Moment and approximation error must be nonnegative')
    if not isinstance(row_count,int) or row_count<1:raise ValueError('A positive admissible row count is required')
    if not isinstance(half_order,int) or half_order<1:raise ValueError('A positive half-order is required')
    if not isinstance(denominator,int) or denominator<1:raise ValueError('A positive rational rounding denominator is required')
    value=moment_upper/row_count;power=2*half_order;low=-1;high=1
    def sufficient(k):return k**power*value.denominator>=value.numerator*denominator**power
    while not sufficient(high):high*=2
    while high-low>1:
        mid=(high+low)//2
        if sufficient(mid):high=mid
        else:low=mid
    return error+Q(high,denominator)


def separated_support_count_bounds(moment_lower,moment_upper,total_weight,amplitude_bound,half_order=1):
    """Transfer a certified moment enclosure into marked-support bounds.

Marked scores must have modulus one; every other score must have modulus
at most amplitude_bound < 1. Weights must be nonnegative and sum to
total_weight. Those universal premises require independent certificates.
"""
    lo,hi,W,delta=map(Q,(moment_lower,moment_upper,total_weight,amplitude_bound))
    if not 0<=lo<=hi or W<0 or lo>W:
        raise ValueError('Nonnegative, consistent moment and total-weight bounds are required')
    if not 0<=delta<1 or type(half_order) is not int or half_order<1:
        raise ValueError('A strict support gap and positive integer half-order are required')
    beta=delta**(2*half_order)
    lower=max(Q(0),(lo-beta*W)/(1-beta));upper=min(W,hi)
    assert lower<=upper
    return {'count_lower':lower,'count_upper':upper,
            'uniform_interval_width_upper':(hi-lo+beta*W)/(1-beta)}


def separated_support_required_order(total_weight,amplitude_bound,rounding_error=0,target_width=1):
    W,delta,error,width=map(Q,(total_weight,amplitude_bound,rounding_error,target_width))
    if W<0 or not 0<=delta<1 or not 0<=error<width:
        raise ValueError('A strict support gap and attainable positive target width are required')
    step=delta*delta;beta=step;k=1
    while (error+beta*W)/(1-beta)>=width:
        beta*=step;k+=1
    return k


def roughness_moment_upper_bound(scale,score_exponent,half_order=1,row_modulus=None):
    """Classical-sieve envelope for scores controlled by the least prime.

Requires |b_n| <= (log P^-(n)/log n)^theta on n in [X,2X].
The imported uniform rough-number theorem and this score law must be
separately certified. A Fourier bound additionally needs distinct residues;
H>=X+1 assures that premise on the complete integer window.
"""
    import flint
    theta=Q(score_exponent)
    if type(scale) is not int or scale<2 or theta<=0 or type(half_order) is not int or half_order<1:
        raise ValueError('An integer scale >= 2, positive score exponent and integer half-order are required')
    if row_modulus is not None and (type(row_modulus) is not int or row_modulus<scale+1):
        raise ValueError('The complete doubling window needs row modulus H >= X+1')
    gamma=2*half_order*theta;L=flint.arb(scale).log()
    def real(x):return flint.arb(x.numerator)/x.denominator
    if gamma>1:
        upper=real(2*gamma/(gamma-1))*scale/L
    elif scale==2:
        upper=flint.arb(2*scale)  # retain the small-scale case explicitly
    elif gamma==1:
        upper=2*scale*(1+L.log())/L
    else:
        upper=real(2/(1-gamma))*scale/L**real(gamma)
    return upper if row_modulus is None else row_modulus*upper


def program_value(program,inputs):
    family=program['family']
    if family=='circle_even_moment':
        return even_moment(inputs[program['input']],program['half_order'])
    if family=='pair_fourth_moment_state':
        return energy_state(inputs[program['left_input']],inputs[program['right_input']])
    if family=='additive_twist_second_moment':
        return additive_twist_energy(inputs[program['input']],program['scale'],program['row_modulus'],program.get('index_degree',1))
    if family=='replicated_row_target_bound':
        return replicated_target_bound(inputs[program['moment_upper_input']],program['row_count'],
                                       inputs[program['error_input']],program.get('half_order',1))
    if family=='separated_support_moment_count_bounds':
        return separated_support_count_bounds(inputs[program['moment_lower_input']],inputs[program['moment_upper_input']],
                                              inputs[program['total_weight_input']],Q(program['amplitude_bound']),
                                              program.get('half_order',1))
    if family=='separated_support_required_order':
        return separated_support_required_order(inputs[program['total_weight_input']],Q(program['amplitude_bound']),
                                                inputs[program['rounding_error_input']],Q(program.get('target_width','1')))
    if family=='prime_roughness_moment_upper_bound':
        return roughness_moment_upper_bound(inputs[program['scale_input']],Q(program['score_exponent']),
                                           program.get('half_order',1),program.get('row_modulus'))
    raise ValueError('Unknown arithmetic family-moment production '+family)


PRODUCTION_CATALOGUE={
    'energy_objects':['complete_coefficient_family','row_twist','circle_polynomial','even_moment',
                      'mixed_energy_state','positive_energy_functional','distinguished_arithmetic_target',
                      'admissible_row_replication','uniform_row_error','separated_score_support',
                      'nonnegative_weighted_coefficient_moment','integer_count_bracket'],
    'scale_operations':['signed_matrix_transfer','phase_shift','state_recurrence','normalized_scale_cost'],
    'inequality_search':['unknown_energy_transfer_coefficients','unknown_positive_metric_weights',
                         'growth_exponent','forcing_term','contraction_margin','resonant_logarithmic_loss'],
    'certificate_backends':['exact_character_orthogonality','complete_residue_bucket_Cauchy_bound',
                            'Laurent_coefficient_identity','frequency_support_separation',
                            'positive_left_eigenfunctional','induction_and_geometric_tail',
                            'Holder_triangle_row_target_transfer','separated_support_affine_endpoint_certificate',
                            'least_prime_score_envelope_and_imported_rough_number_sieve','layer_cake_integrability_and_critical_cost'],
    'ordinary_zeta_gate':'A nonvanishing Mellin numerator and global moment/row-count/error package require separate certificates; none is supplied for a new prime/Mobius estimate',
    'quantifiers':['every_positive_integer_scale','every_row_modulus','every_unit_circle_phase',
                   'every_recursion_level','every_declared_coefficient_input'],
    'scope':'Finite evaluations are not global inequalities; every proposed recurrence needs a universal operator/support certificate',
    'unimplemented_targets':['automatic_enlargement_of_mixed_energy_states',
                             'automatic_Mellin_numerator_nonvanishing_certificates_for_prime_families',
                             'general_Eisenstein_Hecke_family_moments','full_theta_reflection',
                             'new_critical_scale_Mobius_or_prime_cancellation_bound']}
