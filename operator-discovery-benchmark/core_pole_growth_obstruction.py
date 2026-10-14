"""Proof-backed rejection of growth bounds incompatible with a boundary pole.

The generic theorem is in CORE_BOUND_POLE_ORDER_REVIEW_006.txt. Numerical
witnesses use enclosing complex balls; no sampled value is a zero certificate.
The gate leaves a non-rejected hypothesis unproved.
"""
from fractions import Fraction as Q
import json
from flint import acb, acb_series, arb, ctx

CENTRE = ('1/2', '14.13472514173469379046')
RADIUS = '1/100000'
SHIFTS = ('1/3', '2/3')
THETAS = ('0', '1/6', '1/3', '1/2', '2/3', '5/6')


def real(text):
    q = Q(text)
    return arb(q.numerator) / q.denominator


def key(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def certify_local_zero(bits, method, meter):
    """Two sufficient, independently evaluated disk criteria for one simple zero."""
    if bits < 192 or method not in ('rouche', 'newton_contraction'):
        raise ValueError('declared precision and disk criterion')
    old_prec, old_cap = ctx.prec, ctx.cap
    ctx.prec, ctx.cap = bits, 24
    try:
        c = acb(real(CENTRE[0]), real(CENTRE[1]))
        r = real(RADIUS)
        rectangle = c + acb(arb(0, r), arb(0, r))
        f = c.zeta()
        slope = acb_series([c, 1], prec=2).zeta()[1]
        meter.charge(200000)
        if not slope.abs_lower() > 0:
            raise ArithmeticError('nonzero centre derivative required')
        if method == 'rouche':
            second = 2 * acb_series([rectangle, 1], prec=3).zeta()[2]
            margin = slope.abs_lower()*r - f.abs_upper() - second.abs_upper()*r*r/2
            details = dict(centre_residual=f.abs_upper().str(65),
                           derivative_lower=slope.abs_lower().str(65),
                           second_derivative_upper=second.abs_upper().str(65))
        else:
            derivative = acb_series([rectangle, 1], prec=2).zeta()[1]
            contraction = ((derivative-slope)/slope).abs_upper()
            margin = r*(1-contraction) - (f/slope).abs_upper()
            if not contraction < 1:
                raise ArithmeticError('disk derivative contraction required')
            details = dict(contraction_upper=contraction.str(65),
                           newton_displacement_upper=(f/slope).abs_upper().str(65))
        meter.charge(200000)
        if not margin > 0:
            raise ArithmeticError('strict whole-disk existence/uniqueness margin')
        shifted = {}
        for shift in SHIFTS:
            value = (rectangle+real(shift)).zeta()
            meter.charge(100000)
            if not value.abs_lower() > 0:
                raise ArithmeticError('shifted zeta must be nonzero on the whole disk')
            shifted[shift] = dict(value=value.str(65), abs_lower=value.abs_lower().str(65))
        # This extra derivative check gives a nonzero slope at the actual zero
        # and a nonzero Laurent leading coefficient enclosure.
        derivative = acb_series([rectangle, 1], prec=2).zeta()[1]
        meter.charge(100000)
        if not derivative.abs_lower() > 0:
            raise ArithmeticError('simple actual zero derivative')
        leading = real('9/2')*(rectangle+real('1/3')).zeta()/derivative**2
        meter.charge(100000)
        if not leading.abs_lower() > 0:
            raise ArithmeticError('nonzero complete core leading coefficient')
        filters = []
        for sign, theta in [(0, '0')] + [(s, t) for t in THETAS for s in (1, -1)]:
            program = dict(kind='delay', sign=sign, theta=theta)
            multiplier = 1 - sign*(real(theta)*arb(2).log()).exp()*(-rectangle*arb(2).log()).exp()
            meter.charge(10000)
            if not multiplier.abs_lower() > 0:
                raise ArithmeticError('filter noncancellation on actual-zero disk')
            filters.append(dict(filter=program, abs_lower=multiplier.abs_lower().str(65)))
        return dict(method=method, bits=bits, centre=list(CENTRE), radius=RADIUS,
                    margin=margin.str(65), details=details, rectangle=rectangle.str(65),
                    unique_simple_zero=True, critical_real_part='1/2',
                    critical_line_reason='disk invariant under s -> 1-conjugate(s); zeta zero reflection and uniqueness',
                    height_between=[14, 15], shifted_nonvanishing=shifted,
                    actual_zero_derivative_lower=derivative.abs_lower().str(65),
                    core_laurent_leading_abs_lower=leading.abs_lower().str(65),
                    surviving_delays=filters, whole_signed_bound_proved=False, RH_proved=False)
    finally:
        ctx.prec, ctx.cap = old_prec, old_cap


def unique_pole(terms, multiplicity, nonzero_shifts, coefficients):
    """Unique largest negative integral exponent; ambiguous cancellations defer."""
    if type(multiplicity) is not int or multiplicity < 1:
        raise ValueError('certified positive zero multiplicity')
    shifts = set(map(Q, nonzero_shifts))
    degrees = []
    for term in terms:
        if term['coefficient'] not in coefficients:
            raise ValueError('finite source scalar required')
        scalar = arb(coefficients[term['coefficient']])
        if not scalar.is_finite():
            raise ValueError('finite source scalar required')
        powers = {}
        for shift, exponent in term['zeta_factors']:
            q, e = Q(shift), Q(exponent)
            if e.denominator != 1:
                raise ValueError('fractional factors require a separate branch theorem')
            powers[q] = powers.get(q, 0) + int(e)
        for shift, exponent in powers.items():
            if shift and exponent and shift not in shifts:
                raise ValueError('every shifted factor needs a nonvanishing certificate')
        degrees.append(-multiplicity*powers.get(Q(0), 0) if not scalar.is_zero() else -1)
    if not degrees or max(degrees) <= 0 or degrees.count(max(degrees)) != 1:
        return None
    index = degrees.index(max(degrees))
    if arb(coefficients[terms[index]['coefficient']]).contains(0):
        return None
    return dict(rule='unique_dominant_integral_zeta_pole', order=max(degrees),
                leading_term_index=index, term_orders=degrees,
                minimum_dyadic_energy_log_degree=2*max(degrees)-2,
                tied_leading_terms_cancelled=False)


def make_witness(terms, coefficients, producer, checker):
    for record in (producer, checker):
        if (record['centre'] != list(CENTRE) or record['radius'] != RADIUS or
                not record['unique_simple_zero'] or record['critical_real_part'] != '1/2' or
                not arb(record['margin']) > 0):
            raise ValueError('certified matching critical simple zero')
        if set(record['shifted_nonvanishing']) != set(SHIFTS):
            raise ValueError('complete shifted witness')
        if any(not arb(v['abs_lower']) > 0 for v in record['shifted_nonvanishing'].values()):
            raise ValueError('strict shifted nonvanishing')
    if {producer['method'], checker['method']} != {'rouche', 'newton_contraction'}:
        raise ValueError('two distinct disk criteria')
    pole = unique_pole(terms, 1, SHIFTS, coefficients)
    if pole is None:
        raise ValueError('unresolved complete-source pole cancellation')
    left = {key(v['filter']): v for v in producer['surviving_delays']}
    right = {key(v['filter']): v for v in checker['surviving_delays']}
    if set(left) != set(right) or len(left) != 13:
        raise ValueError('same complete filter certificate domains')
    for k in left:
        if not arb(left[k]['abs_lower']) > 0 or not arb(right[k]['abs_lower']) > 0:
            raise ValueError('strict actual-zero multiplier noncancellation')
    return dict(schema='certified-core-pole-growth-obstruction-v1', source_terms=terms,
                source_pole=pole, source_scalar_values=coefficients,
                numerical_witnesses=[producer, checker],
                surviving_filters=[left[k]['filter'] for k in left] + [dict(kind='log_abel', cutoff=64)],
                log_abel_rule='M_G_prime=D_prime/s+entire_head; bounded integer-cell discrepancy; leading pole order preserved',
                log_abel_coefficient_majorant='|f(n)|<= (3*beta+ceil(R_u))*d2(n)',
                proof_reviews=['CORE_BOUND_POLE_ORDER_REVIEW_006.txt', 'CORE_BOUND_CANDIDATE_REVIEW_006.txt'],
                proved_uniform_critical_bound=False, whole_signed_bound_proved=False, RH_proved=False)


def gate(program, rho, gamma, log_power, witness):
    """Apply before ranking: non-rejection is never a proof of the inequality."""
    rho, gamma = Q(rho), Q(gamma)
    if not 0 <= rho <= 1 or gamma < 0 or type(log_power) is not int or log_power < 0:
        raise ValueError('nonnegative recurrence with scale multiplier at most one')
    aux = program['auxiliary']
    if aux is not None:
        if Q(aux['weight']) < 0:
            raise ValueError('nonnegative storage required for target domination')
        for v in aux['coefficients']:
            Q(v)
        Q(aux['alpha'])
        if aux['theta'] is not None:
            Q(aux['theta'])
    if witness['schema'] != 'certified-core-pole-growth-obstruction-v1':
        raise ValueError('bound witness schema')
    retained = key(program['target_filter']) in {key(f) for f in witness['surviving_filters']}
    degree = log_power + int(rho == 1) if gamma == 0 else None
    minimum = witness['source_pole']['minimum_dyadic_energy_log_degree']
    reject = retained and degree is not None and degree < minimum
    return dict(rule='retained_boundary_pole_minimum_log_degree',
                filter_survival_certified=retained, pole_order=witness['source_pole']['order'],
                implied_filtered_energy_log_degree=degree, minimum_log_degree=minimum,
                uniform_shape_disproved=reject,
                status='analytic_countercertificate' if reject else 'not_excluded_by_this_rule',
                independent_of_fitted_constant=True, proved_uniform_critical_bound=False,
                whole_signed_bound_proved=False, RH_proved=False)


def annotate(record, program, witness):
    """Preserve archived finite evidence while making rejection ranking-visible."""
    decision = gate(program, record['rho'], record['gamma'], record['log_power'], witness)
    result = dict(record, critical_pole_gate=decision, prior_status=record['status'])
    if decision['uniform_shape_disproved']:
        result.update(status='analytic_countercertificate', cofinal_candidate=False)
    return result
