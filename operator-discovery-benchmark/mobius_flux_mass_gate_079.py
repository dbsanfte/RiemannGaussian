"""Feed proved growing prime/semiprime modes back into covariance search.

These are negative asymptotic rules for a proposed local bound. They do not
bound the full signed residual from below or supply an effective threshold.
"""
from fractions import Fraction as Q

import mobius_prime_mass_gate_078 as OLD


def logarithm_bounds(alpha, terms=32):
    alpha = Q(alpha)
    if not Q(1, 3) < alpha < Q(1, 2) or terms != 32:
        raise ValueError('fixed finite rational log enclosure domain')
    z = 1-2*alpha
    lower = 2*sum((z**(2*k+1)/(2*k+1) for k in range(terms)), Q(0))
    upper = lower+2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    return lower, upper


def propose_gate(kernel, primes, gamma, q, ray):
    kernel = OLD.canonical_kernel(kernel)
    OLD.F.admit_primes(primes)
    if list(primes) != sorted(primes):
        raise ValueError('sorted fixed excluded primes required')
    if type(ray) is not list or len(ray) != 10:
        raise ValueError('ten ray coefficients required')
    a = list(map(OLD.F.S.B.rational, ray))
    active = {i for i, value in enumerate(a) if value}
    g, exponent = Q(gamma), Q(q)
    if not 1 <= exponent < 2:
        raise ValueError('covariance exponent1<=q<2 required')
    if not active or not active <= {1, 9}:
        return dict(status='UNSUPPORTED_OTHER_SIGNED_CHANNELS', uniform_correlation_proved=False)
    if active == {1}:
        if not 0 < g < 1:
            return dict(status='OUTSIDE_PRIME_SIGNATURE_DOMAIN', uniform_correlation_proved=False)
        signature = (-a[1], -a[1])
        terms = 0
    else:
        if not Q(1, 2) < g < Q(3, 4):
            return dict(status='OUTSIDE_SEMIPRIME_SIGNATURE_DOMAIN', uniform_correlation_proved=False)
        low, high = logarithm_bounds(2*g/3)
        signature = tuple(sorted((-a[1]+a[9]*low, -a[1]+a[9]*high)))
        terms = 32
    mass = sum((Q(row['weight'])/row['divisor'] for row in kernel), Q(0))
    delta = Q(1)
    for p in primes:
        delta *= Q(p-1, p)
    leading = tuple(sorted(mass*delta*x/2 for x in signature))
    if leading[0] <= 0 <= leading[1]:
        return dict(status='UNPAID_ZERO_OR_UNRESOLVED_LEADING_MODE', uniform_correlation_proved=False)
    certificate = dict(mass=str(mass), delta=str(delta), leading_lower=str(leading[0]),
                       leading_upper=str(leading[1]), sigma=str(2-exponent), log_terms=terms)
    return dict(status='FLUX_MASS_OBSTRUCTION_PROPOSAL', certificate=certificate,
        growing_scale='u^(2-q)/log(u)^2 in the necessary covariance price',
        imported_theorem=dict(name='prime number theorem', statement='pi(x)~x/log(x)', source=OLD.PNT_REFERENCE),
        no_finite_kappa_closes_this_uniform_local_leaf=True, effective_finite_threshold_supplied=False,
        arithmetic_residual_refuted=False, uniform_source_bound_proved=False, RH_proved=False)


def feedback(candidate, result, admissions):
    obstructed = [i for i, value in enumerate(admissions) if value.get('status') == 'VERIFIED_FLUX_MASS_OBSTRUCTION']
    constraints = []
    for index in obstructed:
        admission = admissions[index]
        if admission['mode'] == 'prime_last_bin':
            alpha = 2*Q(candidate['gamma'])/3
            constraints.append(dict(leaf_index=index, supported_coordinates=[1, 9],
                leading_signature='folded_mass*(-a1+a9*log((1-alpha)/alpha))/2',
                alpha=str(alpha), logarithm_argument=str((1-alpha)/alpha),
                exact_symbolic_repair_condition='a1=a9*log((1-alpha)/alpha)',
                repair_only_removes_first_asymptotic_mode=True,
                lower_logarithmic_remainders_still_unpaid=True,
                other_channels_require_their_own_signatures=True))
        else:
            constraints.append(dict(leaf_index=index, supported_coordinates=[1],
                leading_signature='-folded_mass*a1/2',
                required_change='couple with signed composite channels or prove a different normalization',
                lower_logarithmic_remainders_still_unpaid=True))
    return dict(schema='signed-covariance-obstruction-feedback-v1', id=candidate['id'],
        source_id=candidate['source_id'], gamma=candidate['gamma'], q=candidate['q'],
        exact_conditional_cover=candidate, finite_leaf_failures=result['leaf_failures'],
        all_scale_obstructed_leaf_indices=obstructed,
        proved_nuisance_mode_constraints=constraints,
        avoid_same_impossible_leaf_with_larger_constant=True,
        target='control signed scale flux after preserving and cancelling growing prime/composite modes jointly',
        next_grammar=['multi-channel arithmetic contrasts with exact or rigorously enclosed coefficient functions',
            'parameterized prime/composite pairings with checked transformed domains',
            'signed cross-moment inequalities whose prices are separately proved',
            'explicit obligations for every prime entry and exit at moving cutoff boundaries'],
        warning='annihilating only the leading u/log(u) mode does not pay its lower logarithmic remainders',
        paid='uniform fixed-kernel coefficient norm, complete recurrence base, exact conditional ray cover',
        unpaid='uniform arithmetic covariance estimates and original source/head/core/RH transfer',
        arithmetic_residual_refuted=False, uniform_correlation_proved=False, RH_proved=False)
