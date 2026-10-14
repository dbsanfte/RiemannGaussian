"""Independent exact AST/tail verification and direct numerical preconditioning.

No producer compiler or prime-local source modes are imported. Tail identities
retain every valuation; recoverable representation changes leave the complete
signed bound and the unsuppressed source mode open.
"""
from fractions import Fraction as Q
from math import ceil, comb, isqrt
import re
from flint import arb, ctx
from check_joint_reciprocal_correlation import State

SHIFTS = ('1/6', '1/3', '1/2', '2/3', '5/6', '1')
POWERS = ('-2', '-1', '-1/2', '1/2', '1', '2')
LABELS = ('B', 'U', 'V', 'power')
MAX_HORIZON = 131071


def _rational(text):
    if type(text) is not str or len(text) > 128 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('canonical rational string')
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational text') from error
    if str(value) != text: raise ValueError('canonical rational string')
    return value


def _expected(shift, power, meter):
    v = _rational(shift); r = _rational(power)
    if shift not in SHIFTS or power not in POWERS + ('0',): raise ValueError('sixth-lattice shift/power grammar')
    words = [('1', '0')] + [(a, b) for a in SHIFTS for b in POWERS]
    if (shift, power) not in words: raise ValueError('zero power is the unique identity word')
    originals = ({Q(0): -2, Q(1, 3): 1, Q(2, 3): 1},
                 {Q(0): -1, Q(1, 3): 1}, {Q(0): -1, Q(2, 3): 1}, {Q(1, 3): 1})
    coefficients = ('beta', '-beta', '-beta', '-R_u'); terms = []
    positive = numerator = Q(0); largest = 0; integral = True
    for name, scalar, source in zip(LABELS, coefficients, originals):
        factors = {s: Q(e) for s, e in source.items()}; factors[v] = factors.get(v, Q(0)) - r
        factors = {s: e for s, e in factors.items() if e}
        meter.charge(12 + 3 * len(factors))
        positive += sum((e for e in factors.values() if e > 0), Q(0))
        numerator += sum((-e for e in factors.values() if e < 0), Q(0))
        largest = max(largest, sum(e > 0 for e in factors.values()))
        integral &= all(e.denominator == 1 for e in factors.values())
        terms.append(dict(name=name, coefficient=scalar, zeta_factors=[[str(s), str(e)] for s, e in sorted(factors.items())]))
    order = ceil(abs(r)); loss = max(Q(1, 2) - v, Q(0))
    if r == 0:
        recovery = dict(cofinal=True, kind='identity', divisor_order=0, energy_power_loss='0', norm_bound='1')
    else:
        recovery = dict(cofinal=loss == 0, kind='bounded' if v > Q(1, 2) else 'polylog' if v == Q(1, 2) else 'unpaid_power',
                        divisor_order=order, energy_power_loss=str(2 * loss),
                        norm_bound='zeta(' + str(v + Q(1, 2)) + ')^' + str(order) if v > Q(1, 2) else 'H^(' + str(loss) + ')*(1+log H)^' + str(order),
                        covers_forward_and_inverse=True, coefficient_majorant='d_' + str(order) + '(n)*n^(-' + str(v) + ')')
    return dict(id=words.index((shift, power)), shift=shift, power=power,
                operator='Dirichlet convolution by coefficients of zeta(s+shift)^(-power)',
                recovery=recovery, terms=terms, positive_factor_order=str(positive), numerator_factor_order=str(numerator),
                max_positive_factors_in_one_term=largest, integral_local_rational_functions=integral,
                correction='(beta*delta-d)*preconditioner, retained with its proved global norm cost',
                whole_signed_bound_proved=False, RH_proved=False)


def _same(left, right):
    if type(left) is not type(right): return False
    if type(left) is dict: return set(left) == set(right) and all(_same(left[k], right[k]) for k in left)
    if type(left) is list: return len(left) == len(right) and all(_same(a, b) for a, b in zip(left, right))
    return left == right


def verify_program(row, meter):
    if type(row) is not dict: raise ValueError('exact program record')
    expected = _expected(row.get('shift'), row.get('power'), meter)
    if not _same(row, expected): raise ValueError('source factor AST/recovery/program metadata mismatch')
    return dict(verified=True, program=row, full_target='OPEN', unsuppressed_source_mode='OPEN', RH_proved=False)


def verify_selection(rows, selected_id, meter):
    if type(rows) is not list or len(rows) != 37 or type(selected_id) is not int: raise ValueError('complete37-word algebraic selection')
    by_id = {}
    for row in rows:
        verify_program(row, meter)
        if row['id'] in by_id: raise ValueError('duplicate grammar word')
        by_id[row['id']] = row
    if set(by_id) != set(range(37)): raise ValueError('missing grammar word')
    eligible = [row for row in by_id.values() if row['recovery']['cofinal']]
    def priority(row):
        return (Q(row['positive_factor_order']), row['max_positive_factors_in_one_term'], not row['integral_local_rational_functions'],
                Q(row['numerator_factor_order']), abs(Q(row['power'])), row['id'])
    chosen = min(eligible, key=priority)
    if chosen['id'] != selected_id: raise ValueError('algebraic selection mismatch')
    return dict(verified=True, selected=chosen, selection_uses_numerical_responses=False, full_target='OPEN', RH_proved=False)


def _multiply(left, right, meter):
    out = {}
    for i, a in left.items():
        for j, b in right.items():
            meter.charge(4); out[i + j] = out.get(i + j, Q(0)) + a * b
    return {i: c for i, c in out.items() if c}


def _poly(rows, meter):
    if type(rows) is not list or len(rows) > 64: raise ValueError('bounded polynomial rows')
    result = {}; previous = -1
    for row in rows:
        if type(row) is not list or len(row) != 2: raise ValueError('power/coefficient row')
        e, text = row
        if type(e) is not int or not previous < e <= 64: raise ValueError('strict ordered polynomial powers')
        coefficient = _rational(text)
        if not coefficient: raise ValueError('omit zero coefficient')
        result[e] = coefficient; previous = e; meter.charge()
    return result


def _local_coefficients(factors, count, meter):
    rows = [{0: Q(1)}] + [{} for _ in range(count)]
    for text, exponent_text in factors:
        shift, exponent = Q(text), Q(exponent_text)
        if exponent.denominator != 1 or (6 * shift).denominator != 1: raise ValueError('integral local language')
        degree = int(6 * shift)
        # Multiply/divide one exact linear Euler factor, at each valuation.
        for _ in range(abs(int(exponent))):
            old = [dict(row) for row in rows]
            if exponent < 0:
                for e in range(1, count + 1):
                    updated = dict(old[e])
                    for p, c in old[e - 1].items(): updated[p + degree] = updated.get(p + degree, Q(0)) - c; meter.charge(3)
                    rows[e] = {p: c for p, c in updated.items() if c}
            else:
                for e in range(1, count + 1):
                    updated = dict(old[e])
                    for p, c in rows[e - 1].items(): updated[p + degree] = updated.get(p + degree, Q(0)) + c; meter.charge(3)
                    rows[e] = {p: c for p, c in updated.items() if c}
    return rows


def verify_tails(row, tails, meter):
    verify_program(row, meter)
    if type(tails) is not dict or set(tails) != {'status', 'terms', 'all_prime_powers_retained', 'whole_signed_bound_proved', 'RH_proved'}:
        raise ValueError('complete certified tail record required')
    if tails['status'] != 'COMPLETE_REPEATED_VALUATION_TAILS_CERTIFIED' or tails['all_prime_powers_retained'] is not True or tails['whole_signed_bound_proved'] is not False or tails['RH_proved'] is not False:
        raise ValueError('tail/proof scope mismatch')
    if type(tails['terms']) is not list or len(tails['terms']) != 4: raise ValueError('all4 source terms retained')
    for term, certificate in zip(row['terms'], tails['terms']):
        if type(certificate) is not dict or certificate.get('name') != term['name'] or certificate.get('tail_start') != 2 or type(certificate.get('cofactor_divisor_order')) is not int or certificate.get('cofactor_divisor_order') != 2:
            raise ValueError('tail source/head/cofactor binding')
        factors = [(Q(s), Q(e)) for s, e in term['zeta_factors']]
        numerator_degree = sum(-int(e) for _, e in factors if e < 0)
        local = _local_coefficients(term['zeta_factors'], max(4, numerator_degree + 2), meter)
        if certificate.get('zero_above_first_valuation') is True:
            expected_keys = {'name', 'zero_above_first_valuation', 'tail_start', 'tail', 'valuation_mass_power', 'cofactor_divisor_order'}
            if any(e > 0 for _, e in factors) or numerator_degree > 1 or set(certificate) != expected_keys or certificate['tail'] != [] or certificate['valuation_mass_power'] is not None or any(local[e] for e in range(2, len(local))):
                raise ValueError('zero tail does not follow from complete Euler numerator')
            continue
        expected_keys = {'name', 'zero_above_first_valuation', 'tail_start', 'tail', 'common_ratio_power', 'factorization', 'valuation_mass_power', 'valuation_mass_constant', 'recurrence', 'first_valuation_bernstein', 'cofactor_divisor_order'}
        if set(certificate) != expected_keys or certificate['zero_above_first_valuation'] is not False: raise ValueError('exact nonzero tail schema')
        positive = [(s, e) for s, e in factors if e > 0]
        if len(positive) != 1 or positive[0][1] != 1 or positive[0][0] <= 0 or numerator_degree > 2:
            raise ValueError('simple positive pole and complete degree<=2 numerator required')
        pole = int(6 * positive[0][0]); tail = _poly(certificate.get('tail'), meter)
        if certificate.get('common_ratio_power') != pole or tail != local[2]: raise ValueError('exact second-valuation tail mismatch')
        for e in range(3, len(local)):
            if local[e] != {p + pole * (e - 2): c for p, c in tail.items()}: raise ValueError('geometric tail recurrence mismatch')
        f = certificate.get('factorization')
        if type(f) is not dict or set(f) != {'monomial_power', 'coefficient', 'one_minus_power', 'multiplicity'}:
            raise ValueError('exact tail factorization schema')
        power, multiplicity = f['monomial_power'], f['multiplicity']; constant = _rational(f['coefficient'])
        if type(power) is not int or not 0 <= power <= 64 or type(multiplicity) is not int or not 1 <= multiplicity <= 8 or f['one_minus_power'] != pole:
            raise ValueError('tail monomial/common-pole factor')
        expanded = {power + pole * j: constant * (-1) ** j * comb(multiplicity, j) for j in range(multiplicity + 1)}
        meter.charge(5 * (multiplicity + 1))
        if expanded != tail or abs(constant) > 1 or certificate.get('valuation_mass_power') != str(Q(power, 6)) or certificate.get('valuation_mass_constant') != str(abs(constant)):
            raise ValueError('expanded tail or geometric mass certificate mismatch')
        if certificate.get('recurrence') != 'coefficient(p^e)=tail(x)*x^(common_ratio_power*(e-2)), x=p^(-1/6), e>=2': raise ValueError('recurrence statement binding')
        bernstein = certificate.get('first_valuation_bernstein')
        degree = max(local[1], default=0)
        if type(bernstein) is not list or len(bernstein) != degree + 1: raise ValueError('complete first-valuation Bernstein coefficients')
        b = [_rational(text) for text in bernstein]
        if any(abs(c) > 2 for c in b): raise ValueError('first valuation bound<=2')
        # Literal expansion of sum b_j*C(d,j)*x^j*(1-x)^(d-j).
        expanded = {}
        for j, coefficient in enumerate(b):
            for k in range(degree - j + 1):
                meter.charge(5)
                e = j + k; expanded[e] = expanded.get(e, Q(0)) + coefficient * comb(degree, j) * comb(degree - j, k) * (-1) ** k
        if {e: c for e, c in expanded.items() if c} != local[1]: raise ValueError('literal Bernstein recomposition mismatch')
    return dict(verified=True, tails=tails, all_prime_powers_retained=True, unsuppressed_source_mode='OPEN', full_target='OPEN', whole_signed_bound_proved=False, RH_proved=False)


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb value')
    return value


def _convolve(left, right, meter):
    out = [arb(0)] * len(left)
    for d in range(1, len(left)):
        for k in range(1, (len(left) - 1) // d + 1):
            out[d * k] = _finite(out[d * k] + _finite(left[d] * right[k], meter), meter); meter.charge(2)
    return out


def _prefix(values, meter):
    out = [arb(0)] * len(values)
    for n in range(1, len(values)): out[n] = _finite(out[n - 1] + values[n], meter)
    return out


def precondition(state, shift, power, meter):
    if ctx.prec != 192 or not isinstance(state, State) or state.get('precision') != 192: raise ValueError('own192-bit actual source State')
    v, r = _rational(shift), _rational(power)
    if shift not in SHIFTS or power not in POWERS + ('0',): raise ValueError('sixth-lattice numerical shift/power')
    H = state.get('H')
    if type(H) is not int or not 1 <= H <= MAX_HORIZON: raise ValueError('completeH1..131071')
    for key in ('tilde_b', 'a', 'au', 'd', 'mu'):
        if type(state.get(key)) is not list or len(state[key]) != H + 1: raise ValueError('complete source rows')
    meter.live(44 * (H + 1) + 4096)
    table = [0] * (H + 1); meter.charge(H + 1)
    for p in range(2, isqrt(H) + 1):
        if table[p]: continue
        for n in range(p * p, H + 1, p):
            meter.charge()
            if not table[n]: table[n] = p
    kernels = [[arb(0)] * (H + 1) for _ in range(2)]; kernels[0][1] = kernels[1][1] = arb(1)
    local = {}
    for n in range(2, H + 1):
        residual = n; factors = []
        while residual > 1:
            p = table[residual] or residual; exponent = 0; meter.charge()
            while residual % p == 0: residual //= p; exponent += 1; meter.charge(2)
            factors.append((p, exponent))
        for p, exponent in factors:
            if p not in local:
                meter.charge(64); root = _finite(arb(p).root(6), meter)
                degree = int(6 * v); meter.charge(degree + 2)
                weight = _finite(1 / root ** degree, meter)
                local[p] = ([arb(1)], [arb(1)], weight, Q(1), Q(1))
            left, right, weight, binomial, inverse_binomial = local[p]
            while len(left) <= exponent:
                e = len(left); binomial *= (r - e + 1) / e; inverse_binomial *= (-r - e + 1) / e; meter.charge(6)
                meter.charge(e + 4); monomial = _finite((-weight) ** e, meter)
                left.append(_finite(arb(binomial.numerator) / binomial.denominator * monomial, meter))
                right.append(_finite(arb(inverse_binomial.numerator) / inverse_binomial.denominator * monomial, meter))
                local[p] = (left, right, weight, binomial, inverse_binomial)
        for index in range(2):
            coefficient = arb(1)
            for p, exponent in factors: coefficient = _finite(coefficient * local[p][index][exponent], meter)
            kernels[index][n] = coefficient
    kernel, inverse = kernels
    w = _convolve(kernel, state['tilde_b'], meter); reconstructed = _convolve(inverse, w, meter)
    residual = [_finite(a - b, meter) for a, b in zip(reconstructed, state['tilde_b'])]
    result = dict(H=H, shift=shift, power=power, kernel=kernel, inverse=inverse, w=w,
                  prefix=_prefix(w, meter), reconstructed=reconstructed, reconstruction_residual=residual,
                  whole_signed_bound_proved=False, RH_proved=False, full_target='OPEN', unsuppressed_source_mode='OPEN')
    if shift == '2/3' and power == '1':
        mu = list(map(arb, state['mu'])); ku = [arb(0)] * (H + 1); mu_v = [arb(0)] * (H + 1)
        for n in range(1, H + 1):
            meter.charge(64); root = _finite(arb(n).root(3), meter)
            ku[n] = _finite(1 / root, meter); mu_v[n] = _finite(mu[n] * _finite(ku[n] * ku[n], meter), meter)
        nu0 = _convolve(mu, state['au'], meter); nu1 = _convolve(mu_v, state['au'], meter)
        nu2 = _convolve(mu_v, ku, meter); overlap = _convolve(state['d'], mu_v, meter)
        correction = [arb(0)] * (H + 1); core = [arb(0)] * (H + 1)
        complete_source = [arb(0)] * (H + 1); beta = arb(9) / 2
        for n in range(1, H + 1):
            correction[n] = _finite(beta * mu_v[n] - overlap[n], meter); meter.charge(2)
            core[n] = _finite(beta * nu0[n] - beta * nu1[n] - beta * mu[n] - state['R_u'] * nu2[n], meter); meter.charge(7)
            complete_source[n] = _finite(core[n] + correction[n], meter)
            if not complete_source[n].overlaps(w[n]): raise ArithmeticError('complete selected core/paid correction identity')
        correction_prefix = _prefix(correction, meter)
        result.update(nu0=nu0, nu1=nu1, nu2=nu2, mu=mu, correction=correction, core=core, complete_source=complete_source,
                      core_plus_correction=complete_source, core_prefix=_prefix(core, meter), correction_prefix=correction_prefix,
                      core_residual=[_finite(a - b, meter) for a, b in zip(complete_source, w)],
                      mode_prefixes={name: _prefix(values, meter) for name, values in (('nu0', nu0), ('nu1', nu1), ('nu2', nu2), ('mu', mu))})
        result['mode_prefixes']['correction'] = correction_prefix
        result['complete_source_residual'] = result['core_residual']
        result['identity_residual'] = result['core_residual']
    return result
