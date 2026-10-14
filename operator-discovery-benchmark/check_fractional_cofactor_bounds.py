"""Independent admission of rational coefficient twists and signed recovery.

The frozen cofactor checker supplies exact all-valuation source laws. This
module derives complete partial-prefix estimates, block energies and the
cost of undoing a coefficient twist; it imports no search producer.
"""
from fractions import Fraction as F

import check_prime_cofactor_discovery as C


def _ceil(q):
    return (q.numerator + q.denominator - 1) // q.denominator


def _energy(K, a, ell, meter):
    C._require(K >= 0 and a >= 0 and type(ell) is int and ell >= 0,
               'nonnegative complete-prefix envelope')
    shift = 2 * _ceil(a) + 2 * ell
    C._require(shift <= 32768, 'energy constant exceeds verifier rational resource limit')
    constant = C._checked(K * K * F(1 << shift), meter)
    return dict(constant=str(constant), power=str(C._checked(2*a-1, meter)),
                log_power=2*ell)


def _candidate(bound, gamma, meter):
    """Replay a *verified* source frontier; never a standalone lower premise."""
    J = C._q(bound['unit_ceiling'], meter)
    D = C._q(bound['coefficient_ceiling'], meter)
    original = C._q(bound['energy_upper_exponent'], meter)
    r = None if bound['r'] is None else C._checked(C._q(bound['r'], meter)+gamma, meter)
    # The unit persists. Positive n^-gamma does not change any prime sign.
    if r is None:
        a, ell, K = F(0), 0, J
    elif r < 1:
        a, ell, K = 1-r, 0, C._checked(J+D/(1-r), meter)
    elif r == 1:
        a, ell, K = F(0), 1, C._checked(J+D, meter)
    else:
        a, ell, K = F(0), 0, C._checked(J+D*(1+1/(r-1)), meter)
    weighted = _energy(K, a, ell, meter)
    # Signed Abel uses the whole partial-prefix envelope at one fixed y.
    # gamma/(a+gamma)<=1; gamma=0 is the exact identity, with no factor2.
    recovered_a = C._checked(a+gamma, meter)
    recovered_K = C._checked(K if gamma == 0 else 2*K, meter)
    recovered = _energy(recovered_K, recovered_a, ell, meter)
    lower = None
    if r is not None and r < 1 and bound['sign'] != 0:
        lower = dict(power=str(1-2*r), log_power=-2,
            coefficient_floor=bound['coefficient_floor'], sign=bound['sign'],
            q_threshold=bound['q_threshold'], prime_exponent=str(r),
            unit_ceiling=bound['unit_ceiling'],
            constant='(log(2)/8)^2*A^2/(64*2^(2*r))',
            domain='cofinal integer X with the checked sign/count/unit head conditions')
    prime_powers = []
    for degree, constant, R in bound['prime_polynomial']:
        meter.charge()
        prime_powers.append([str(C._checked(F(degree, 6)+gamma, meter)), constant, R])
    gain = C._checked(original-F(recovered['power']), meter)
    return dict(state=bound['state'], gamma=str(gamma),
        program=dict(op='coefficient_twist', state=bound['state'], exponent=str(gamma)),
        definition='h_gamma(n)=n^(-gamma)*h(n), n>=1',
        prime_powers=prime_powers, effective_prime_exponent=None if r is None else str(r),
        unit_ceiling=str(J), valuation_law=dict(base='verified_prime_cofactor_transfer',
            coefficient_multiplier='p^(-gamma*e)', includes_all_valuations=True,
            cofactor_coprime=True, unit_preserved=True),
        prefix_upper=dict(constant=str(K), power=str(a), log_power=ell,
            scope='every real partial prefix 1<=t<=2X at the same y=ceil(sqrt(2X))'),
        energy_upper=weighted, energy_lower=lower,
        recovery=dict(rule='complete_signed_prefix_Abel',
            identity='A_0(n;y)=n^gamma*A_gamma(n;y)-gamma*integral_1^n A_gamma(t;y)*t^(gamma-1)dt',
            requires_all_partial_prefixes=True, fixed_cutoff=True, unit_retained=True,
            prefix_upper=dict(constant=str(recovered_K), power=str(recovered_a), log_power=ell),
            energy_upper=recovered, original_rough_energy_power=str(original),
            recovered_power_gain=str(gain), strict_power_improvement=bool(gain > 0)),
        scope='raw rough component and its unweighted recovery only',
        paid_joined_core=False, whole_signed_bound_proved=False, RH_proved=False)


def _scope(candidate):
    lower = candidate['energy_lower']
    heads = None
    if lower is not None:
        q0 = F(lower['q_threshold'])
        heads = dict(c='log(2)/8', A=lower['coefficient_floor'],
            J=lower['unit_ceiling'], r=lower['prime_exponent'],
            requirements=['X>=16', 'y=ceil(sqrt(2*X))', 'y>='+str(_ceil(q0**-6)),
                          'y<=c*X/(2*log(X))',
                          'J<=c*A*X^(1-r)/(8*2^r*log(X))'],
            quantifier='all integer X beyond one finite uniform head',
            prime_count_provider='elementary central-binomial bound; no PNT or RH')
    return dict(state=candidate['state'], gamma=candidate['gamma'],
        support='one shared y=ceil(sqrt(2*X)); unit and primes for every real 1<=t<=2X',
        raw_energy='X^-2*sum_(X<=n<2X) abs(A_gamma(n;y))^2',
        upper_domain='every integer X>=1', lower_head=heads,
        recovery='signed Abel identity at the same fixed cutoff, on every partial prefix',
        optimal_recovered_bound_claimed=False, joined_core_payment=False)


def verify(base_source, base_certificate, proposal, meter=None):
    """License the base once, then replay every exponent x state certificate."""
    meter = C._meter(meter)
    base = C.verify(base_source, base_certificate, meter)
    C._require(type(proposal) is dict and set(proposal) == {
        'schema', 'base_source', 'base_states', 'exponents', 'candidates',
        'exponent_semantics', 'weighted_bound_scope', 'recovered_strict_power_improvements',
        'operations', 'whole_signed_bound_proved', 'RH_proved'}, 'complete fractional search schema')
    C._require(proposal['schema'] == 'fractional-cofactor-bounds-v1', 'fractional schema version')
    C._require(C._same(proposal['base_source'], base_source) and
               C._same(proposal['base_states'], base_certificate['states']),
               'immutable complete source and proven states')
    data = proposal['exponents']
    C._require(type(data) is list and 1 <= len(data) <= 4096, 'bounded nonempty exponent enumeration')
    exponents = [C._q(value, meter) for value in data]
    C._require(all(g >= 0 for g in exponents) and len(set(exponents)) == len(exponents),
               'distinct exact nonnegative rational coefficient exponents')
    expected = [_candidate(bound, gamma, meter) for gamma in exponents
                for bound in base['frontier_bounds']]
    C._require(C._same(proposal['candidates'], expected),
               'complete ordered exponent/state coverage and signed recovery costs')
    fixed = dict(exponent_semantics='all exact nonnegative rationals; no denominator ceiling',
        weighted_bound_scope='unit and primes at a common rough cutoff',
        recovered_strict_power_improvements=sum(c['recovery']['strict_power_improvement'] for c in expected),
        operations=200*len(expected), whole_signed_bound_proved=False, RH_proved=False)
    C._require(all(C._same(proposal[key], value) for key, value in fixed.items()),
               'exact search accounting and no forged joined or global closure')
    return dict(verified=True, candidates_verified=len(expected), exponents=data,
        all_valuations_retained=True, signed_inverse_Abel_proved=True,
        theorem_scope=[_scope(candidate) for candidate in expected],
        recovered_strict_power_improvements=fixed['recovered_strict_power_improvements'],
        R_enclosure=base['R_enclosure'], scope='raw rough components and complete signed recovery only',
        whole_prefix_bound_proved=False, paid_joined_core=False,
        whole_signed_bound_proved=False, RH_proved=False)
