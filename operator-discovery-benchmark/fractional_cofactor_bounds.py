"""Search rational coefficient weights with explicit recovery costs.

The exponent is an exact Fraction, not a degree on a fixed root lattice.
Weighted rough-prefix bounds use the checked prime polynomial; the signed
Abel identity prices recovery to the unweighted rough prefix. None of these
component estimates pays the joined original core.
"""
from fractions import Fraction as F


def rational(value):
    if isinstance(value, (float, bool)):
        raise ValueError('exact rational exponent required')
    return F(value)


def ceiling(value):
    return -(-value.numerator//value.denominator)


def energy_bound(constant, power, log_power):
    """Convert a complete partial-prefix bound to one whole dyadic block."""
    return dict(constant=str(constant**2*2**(2*ceiling(power)+2*log_power)),
                power=str(2*power-1), log_power=2*log_power)


def candidate(frontier, gamma):
    gamma = rational(gamma)
    if gamma < 0:
        raise ValueError('this bound provider requires nonnegative twists')
    index = frontier['state']
    J, D = map(F, (frontier['unit_ceiling'], frontier['coefficient_ceiling']))
    exponent = None if frontier['r'] is None else F(frontier['r'])+gamma
    if exponent is None:
        power, log_power, K = F(0), 0, J
    elif exponent < 1:
        power, log_power = 1-exponent, 0
        K = J+D/(1-exponent)
    elif exponent == 1:
        power, log_power, K = F(0), 1, J+D
    else:
        power, log_power = F(0), 0
        K = J+D*(1+1/(exponent-1))
    weighted_energy = energy_bound(K, power, log_power)
    recovered_power = power+gamma
    recovered_constant = K if gamma == 0 else 2*K
    recovered_energy = energy_bound(recovered_constant, recovered_power, log_power)
    lower = None
    if exponent is not None and exponent < 1 and frontier['sign']:
        lower = dict(power=str(1-2*exponent), log_power=-2,
            coefficient_floor=frontier['coefficient_floor'],
            sign=frontier['sign'], q_threshold=frontier['q_threshold'],
            prime_exponent=str(exponent), unit_ceiling=frontier['unit_ceiling'],
            constant='(log(2)/8)^2*A^2/(64*2^(2*r))',
            domain='cofinal integer X with the checked sign/count/unit head conditions')
    baseline = F(frontier['energy_upper_exponent'])
    gain = baseline-F(recovered_energy['power'])
    return dict(state=index, gamma=str(gamma),
        program=dict(op='coefficient_twist', state=index, exponent=str(gamma)),
        definition='h_gamma(n)=n^(-gamma)*h(n), n>=1',
        prime_powers=[[str(F(degree, 6)+gamma), a, b]
                      for degree, a, b in frontier['prime_polynomial']],
        effective_prime_exponent=None if exponent is None else str(exponent),
        unit_ceiling=str(J),
        valuation_law=dict(base='verified_prime_cofactor_transfer',
            coefficient_multiplier='p^(-gamma*e)', includes_all_valuations=True,
            cofactor_coprime=True, unit_preserved=True),
        prefix_upper=dict(constant=str(K), power=str(power), log_power=log_power,
            scope='every real partial prefix 1<=t<=2X at the same y=ceil(sqrt(2X))'),
        energy_upper=weighted_energy, energy_lower=lower,
        recovery=dict(rule='complete_signed_prefix_Abel',
            identity='A_0(n;y)=n^gamma*A_gamma(n;y)-gamma*integral_1^n A_gamma(t;y)*t^(gamma-1)dt',
            requires_all_partial_prefixes=True, fixed_cutoff=True, unit_retained=True,
            prefix_upper=dict(constant=str(recovered_constant), power=str(recovered_power),
                              log_power=log_power),
            energy_upper=recovered_energy,
            original_rough_energy_power=str(baseline),
            recovered_power_gain=str(gain),
            strict_power_improvement=bool(gain > 0)),
        scope='raw rough component and its unweighted recovery only',
        paid_joined_core=False, whole_signed_bound_proved=False, RH_proved=False)


def search(base_certificate, exponents):
    exponents = [rational(x) for x in exponents]
    if any(x < 0 for x in exponents) or len(exponents) != len(set(exponents)):
        raise ValueError('distinct nonnegative rational exponents')
    candidates = [candidate(bound, gamma) for gamma in exponents
                  for bound in base_certificate['frontier_bounds']]
    return dict(schema='fractional-cofactor-bounds-v1',
        base_source=base_certificate['source'], base_states=base_certificate['states'],
        exponents=list(map(str, exponents)), candidates=candidates,
        exponent_semantics='all exact nonnegative rationals; no denominator ceiling',
        weighted_bound_scope='unit and primes at a common rough cutoff',
        recovered_strict_power_improvements=sum(c['recovery']['strict_power_improvement']
                                               for c in candidates),
        operations=200*len(candidates),
        whole_signed_bound_proved=False, RH_proved=False)
