"""Executable obstruction feedback: coherent controls and exact pairing leaves.

No075 outcome is changed. New controls still owe their innovation estimate.
"""
from fractions import Fraction as Q
from functools import lru_cache

import mobius_prime_moment_075 as S


def merged_children(parent, operator, beta, prime_groups, direct_children):
    """Merge literal prime multiplicities and direct collisions before squaring.

    prime_groups is one {child: number_of_primes} map per prime coordinate.
    This algebra routine requires separately admitted arithmetic counts.
    """
    if type(parent) is not int or parent < 2 or len(operator) != len(beta) or len(operator) != len(prime_groups)+len(direct_children):
        raise ValueError('complete parent/operator/group data')
    v, t = {}, {}
    groups = list(prime_groups)+[{j: 1} for j in direct_children]
    for a, b, group in zip(map(Q, operator), map(Q, beta), groups):
        if b < 0:
            raise ValueError('nonnegative paid diagonal')
        for j, multiplicity in group.items():
            if type(j) is not int or not 0 <= j < parent or type(multiplicity) is not int or multiplicity < 0:
                raise ValueError('literal smaller-child prime multiplicities')
            if j and multiplicity:
                v[j] = v.get(j, Q(0)) + a*multiplicity
                t[j] = t.get(j, Q(0)) + b*multiplicity
    return {j: x for j, x in v.items() if x}, {j: x for j, x in t.items() if x}


def coherence_price(v, t):
    unsupported = sorted(j for j, a in v.items() if a and not t.get(j, 0))
    if any(b < 0 for b in t.values()):
        raise ValueError('nonnegative diagonal')
    if unsupported:
        return dict(status='ARITHMETIC_RELATION_REQUIRED', unsupported_children=unsupported,
                    arbitrary_child_vector_control_proved=False, actual_arithmetic_refuted=False)
    K = sum((a*a/t[j] for j, a in v.items() if a), Q(0))
    return dict(status='UNIVERSAL_WEIGHTED_CAUCHY', K=str(K),
                arbitrary_child_vector_control_proved=True, original_unit_price_proved=K<=1,
                required_induction_price='K times the complete paid moment price',
                uniform_in_parent_proved=False)


def pairing(v, anchor=None):
    """Greedy opposite-sign pairing, with every unmatched mass paid at an anchor."""
    v = {int(j): Q(a) for j, a in v.items() if a}
    if not v or any(j < 1 for j in v):
        raise ValueError('nonempty positive child support')
    anchor = min(v) if anchor is None else anchor
    if type(anchor) is not int or anchor < 1:
        raise ValueError('positive anchor')
    positive = [[j, a] for j, a in sorted(v.items()) if a > 0]
    negative = [[j, -a] for j, a in sorted(v.items()) if a < 0]
    edges, i, k = [], 0, 0
    while i < len(positive) and k < len(negative):
        amount = min(positive[i][1], negative[k][1])
        edges.append(dict(left=positive[i][0], right=negative[k][0], weight=str(amount)))
        positive[i][1] -= amount
        negative[k][1] -= amount
        i += positive[i][1] == 0
        k += negative[k][1] == 0
    for j, a in positive[i:]:
        if a and j != anchor:
            edges.append(dict(left=j, right=anchor, weight=str(a)))
    for j, a in negative[k:]:
        if a and j != anchor:
            edges.append(dict(left=anchor, right=j, weight=str(a)))
    return dict(anchor=anchor, anchor_coefficient=str(sum(v.values(), Q(0))), edges=edges)


def verify_pairing(parent, v, certificate):
    """Exact conservation is an identity, not a bound on the difference energy."""
    anchor = certificate['anchor']
    if type(anchor) is not int or not 1 <= anchor < parent:
        return False
    rebuilt = {anchor: S.B.rational(certificate['anchor_coefficient'])}
    for edge in certificate['edges']:
        left, right = edge['left'], edge['right']
        if any(type(j) is not int or not 1 <= j < parent for j in (left, right)):
            return False
        a = S.B.rational(edge['weight'])
        rebuilt[left] = rebuilt.get(left, Q(0))+a
        rebuilt[right] = rebuilt.get(right, Q(0))-a
    return {j: a for j, a in rebuilt.items() if a} == {j: Q(a) for j, a in v.items() if a}


def normalized_control(record, spec, exponent, base_u=4096, sign=1):
    """Generate a new operator; never reuse the refuted operator's residual C.

    L_gamma(u)=sum a_i B_i(u)/max(1,n_i(u))^gamma. Direct n_i=1.
    For gamma>=1/2 Cauchy pays the whole correlation uniformly.
    Smaller gamma remains available with an explicit unpaid count factor.
    """
    gamma = S.B.rational(exponent)
    if gamma < 0 or type(sign) is not int or sign not in (-1, 1):
        raise ValueError('nonnegative rational count exponent')
    shape = list(map(S.B.rational, record['shape']))
    if len(shape) != len(S.labels(spec)) or not any(shape):
        raise ValueError('nonzero complete operator')
    beta = S.cauchy_beta(shape)
    prices = S.price_bounds(spec, base_u)
    amplitude = -S.amplitudes(S.dot(beta, prices))[0]
    a = [sign*amplitude*x for x in shape]
    paid = [amplitude*amplitude*x for x in beta]
    rho = S.dot(paid, prices)
    registered = gamma >= Q(1, 2)
    return dict(schema='count-normalized-control-obligation-v1', source_spec=spec,
        origin_record=record['id'], gamma=str(gamma), sign=sign, operator=list(map(str, a)), beta=list(map(str, paid)),
        count_convention='max(1, actual block prime count); direct count1; empty block sum0',
        base_u=base_u, price_bounds=list(map(str, prices)),
        rho_upper=str(rho) if registered else None,
        sqrt_rho_upper=str(S.sqrt_upper(rho)) if registered else None,
        universal_correlation_proved=registered,
        correlation='L_gamma^2 <= sum beta_i max(1,n_i)^(1-2gamma) Q_i',
        unnormalized_moment_control_proved=registered,
        unpaid_count_price=None if registered else 'bound sum beta_i n_i^(1-2gamma) H_i uniformly; old rho is invalid',
        innovation=dict(status='NEW_OPERATOR_REQUIRES_NEW_BOUND', formula='(G-L_gamma)^2 <= C u^q for all u>base_u',
                        inherited_C=None),
        numerically_searched=False, uniform_source_bound_proved=False, RH_proved=False)


@lru_cache(maxsize=100000)
def count_power_bounds(n, gamma, precision=20):
    """Certified arbitrary nonnegative rational powers for variable coefficients."""
    if type(n) is not int or n < 1 or not 8 <= precision <= 24 or gamma < 0:
        raise ValueError('positive count and bounded precision')
    a, b = gamma.numerator, gamma.denominator
    if n.bit_length()*a+precision*b > 100000:
        raise ValueError('power intermediate work/bit gate')
    if b == 1:
        return Q(n**a), Q(n**a)
    target = (n**a) << (precision*b)
    root = int(S.B.fmpz(target).root(b))
    if not root**b <= target < (root+1)**b:
        raise ArithmeticError('exact count power root')
    lo = Q(root, 1 << precision)
    return lo, lo if root**b == target else Q(root+1, 1 << precision)


def operator_enclosure(control, row, precision=20):
    a = list(map(S.B.rational, control['operator']))
    gamma = S.B.rational(control['gamma'])
    if len(a) != len(row['components']) or len(a) != len(row['counts']):
        raise ValueError('complete source row')
    lo = hi = Q(0)
    for coefficient, value, count in zip(a, row['components'], row['counts']):
        if type(count) is not int or count < 0 or (count == 0 and value != 0):
            raise ValueError('literal count and empty block sum')
        lower, upper = count_power_bounds(max(1, count), gamma, precision)
        numerator = coefficient*value
        terms = numerator/lower, numerator/upper
        lo += min(terms)
        hi += max(terms)
    return lo, hi


def generate_feedback(records, spec, exponents=('1/3', '1/2', '17/31', '2/3', '1', '3/2')):
    failed = [r for r in records if r['kind'] != 'direct_only' and r['adaptation_correlation']['status'] == 'REFUTED']
    controls = [normalized_control(r, spec, g, sign=sign) for r in failed for g in exponents for sign in (-1, 1)]
    return dict(schema='coherent-prime-control-feedback-v1', source_spec=spec,
        input_failed_prime_controls=[r['id'] for r in failed], controls=controls,
        normalized_operator_grammar_generated=True, next_numerical_search_run=False,
        competing_branch=dict(grammar='merged quotient weights -> rational flow pairing + paid anchor + signed difference energy',
            exact_conservation_checker='verify_pairing',
            uniform_difference_energy_proved=False,
            unresolved_arithmetic_relationships_are_retained=True),
        uniform_source_bound_proved=False, RH_proved=False)
