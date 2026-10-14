"""Independent exact periodic normalization/cost admission.

No current producer is imported. Critical mu moments are analytic constants;
only the periodic and absolutely shifted moments are ordinary moments here.
"""
from collections import Counter
from fractions import Fraction as F
from math import comb

from flint import arb, ctx
import check_source_pole_guard as POLE


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _fraction(value, meter):
    return POLE._q(value, meter)


def _atoms_from_source(channel, lattice):
    net = Counter()
    for atom in channel['atoms']:
        net[F(atom['shift'], lattice)] += 1 if atom['kind'] == 'power' else -1
    return [{'kind': 'power' if n > 0 else 'mu', 'shift': str(s)}
            for s, n in sorted(net.items()) for _ in range(abs(n))]


def _canonical(atoms):
    net = Counter()
    for atom in atoms:
        net[F(atom['shift'])] += 1 if atom['kind'] == 'power' else -1
    return [{'kind': 'power' if n > 0 else 'mu', 'shift': str(s)}
            for s, n in sorted(net.items()) for _ in range(abs(n))]


def _family(source, meter):
    # Independent old source parser supplies strict source syntax, not a search.
    POLE._derive(source, meter)
    _require(len(source['channels']) == 4, 'complete four-channel source family')
    atoms = [_atoms_from_source(c, source['lattice']) for c in source['channels']]
    r_set = {F(a['shift']) for c in atoms for a in c if a['kind'] == 'power'}
    v_set = {F(a['shift']) for c in atoms for a in c if a['kind'] == 'mu' and F(a['shift']) > 0}
    _require(len(r_set) == len(v_set) == 1, 'one common source power and shifted inverse')
    r, v = next(iter(r_set)), next(iter(v_set))
    _require(0 < r < F(1, 2) and r < v < 1, 'periodic source-family parameter domain')
    atom = lambda k, s: {'kind': k, 'shift': str(s)}
    signatures = [[atom('power', r), atom('mu', 0), atom('mu', 0)],
                  [atom('power', r), atom('mu', 0), atom('mu', v)],
                  [atom('power', r), atom('mu', v)], [atom('mu', 0)]]
    roles = []
    for signature in signatures:
        matches = [i for i, row in enumerate(atoms) if row == _canonical(signature)]
        _require(len(matches) == 1, 'every distinct full signed source role')
        roles.append(matches[0])
    beta = _fraction(source['channels'][roles[0]]['weight'][0], meter)
    _require(beta > 0 and [source['channels'][i]['weight'] for i in roles] ==
             [[str(beta), '0'], [str(-beta), '0'], ['0', '-1'], [str(-beta), '0']],
             'source beta, R coefficient, signs and unit retained')
    return {'beta': str(beta), 'r': str(r), 'v': str(v), 'theta': str(1-r),
            'channel_roles': roles}


def _hyperbola(theta, v, meter):
    lines = [(F(0), F(1)), (theta, -theta)]
    vertices = {theta}
    for i, (a, b) in enumerate(lines):
        for c, d in lines[i+1:]:
            meter.charge()
            if b != d:
                t = (c-a)/(b-d)
                if 0 < t <= theta:
                    vertices.add(t)
    rows = [{'alpha': str(t), 'power': str(max(a+b*t for a, b in lines))}
            for t in sorted(vertices)]
    best = min(rows, key=lambda row: (F(row['power']), F(row['alpha'])))
    minimum, alpha = F(best['power']), F(best['alpha'])
    # A convex combination of the affine errors is a global lower bound.
    dual = [theta/(1+theta), 1/(1+theta)]
    _require(sum(dual) == 1 and sum(w*b for w, (a, b) in zip(dual, lines)) == 0 and
             sum(w*a for w, (a, b) in zip(dual, lines)) == minimum and
             0 < alpha <= theta and minimum <= theta, 'independent global minimax lower certificate')
    exponents = {minimum}
    boundary = 1-v
    if v+minimum <= 1 and boundary < F(1, 2):
        exponents.add((boundary+F(1, 2))/2)
    choices = [{'power': str(s), 'admissible': v+s > 1}
               for s in sorted(exponents) if minimum <= s <= theta]
    admissible = [F(row['power']) for row in choices if row['admissible']]
    sigma = min(admissible) if admissible else minimum
    return {'lines': [{'constant': str(a), 'slope': str(b)} for a, b in lines],
            'domain': '0<alpha<=theta', 'vertices': rows,
            'selected_alpha': best['alpha'], 'envelope_minimum': best['power'],
            'exponent_candidates': choices, 'selected_exponent': str(sigma),
            'critical_shift_margin': str(v+sigma-1), 'subcritical': sigma < F(1, 2),
            'absolute_shift_contraction': v+sigma > 1,
            'proof': 'minimum of convex piecewise-linear exponent envelope at a vertex',
            'all_real_kernel_rule': 'hyperbola_with_complete_periodic_prefix_and_ordinary_tail',
            'kernel_constant_per_prefix_bound': str(7/theta)}


def _periodic(q):
    return {'q': q, 'step_coefficients': [[1, '1'], [q, str(-q)]],
            'solved_mean_equation': ['1', str(F(1, q))], 'periodic_mean': '0',
            'prefix_bound': str(q-1), 'prefix_exact': 'floor(x)-q*floor(x/q)',
            'prefix_domain': 'every real x>=0', 'prefix_nonnegative': True,
            'identity': 'mu*A_q=D_q', 'dirichlet_product': '(1-q^(1-s))*zeta(s)',
            'ordinary_moment_domain': 'Re(s)>0'}


def _dilation(q, power):
    return [[q**i, str(comb(power, i)*(-q)**i)] for i in range(power+1)]


def _transform(source, power, meter):
    result = []
    for i, channel in enumerate(source['channels']):
        atoms = _atoms_from_source(channel, source['lattice'])
        inverse = {'kind': 'mu', 'shift': '0'}
        copies = min(power, atoms.count(inverse))
        for _ in range(copies):
            atoms.remove(inverse)
        meter.charge(1+len(atoms))
        result.append({'source_channel': i, 'atoms': atoms, 'weight': channel['weight'][:],
                       'periodic_copies': power-copies, 'dilation_power': copies,
                       'complete_prefix': True, 'unit_retained': True})
    return result


def _price(channel, family, q, hyperbola, bound, meter):
    r, v, theta = (F(family[k]) for k in ('r', 'v', 'theta'))
    sigma = F(hyperbola['selected_exponent'])
    a, b = map(F, channel['weight'])
    weight = abs(a)+bound*abs(b)
    atoms, periods, degree = channel['atoms'], channel['periodic_copies'], channel['dilation_power']
    stencil = _dilation(q, degree)
    common = {'source_channel': channel['source_channel'], 'weight_ceiling': str(weight),
              'full_dilation': stencil, 'domain': 'every real x>0'}
    power_atom = {'kind': 'power', 'shift': str(r)}
    shifted = _canonical([power_atom, {'kind': 'mu', 'shift': str(v)}])
    if not atoms and not periods:
        partial = F(0)
        maximum = F(0)
        for d, c in stencil:
            partial += F(c)
            maximum = max(maximum, abs(partial))
        constant, rho, rule = weight*maximum, F(0), 'complete_finite_step_prefix'
    elif not atoms and periods == 1:
        constant, rho, rule = weight*(q-1)*(1+q)**degree, F(0), 'periodic_prefix'
    elif atoms == [power_atom] and not periods:
        constant, rho, rule = weight*(1+q)**degree/theta, F(0), 'centered_power_kernel'
    elif atoms == shifted and not periods:
        # Complete mass and tail of the absolutely shifted inverse, all-real.
        kernel = (1/(1-v)+1/(v-r)+1)/theta
        constant, rho, rule = weight*(1+q)**degree*kernel, 1-v, 'centered_shifted_inverse_kernel'
    elif atoms == shifted and periods == 1 and v+sigma > 1:
        kernel = 7*(q-1)/theta*(1+1/(v+sigma-1))
        constant, rho, rule = weight*(1+q)**degree*kernel, sigma, 'periodic_center_then_absolute_shifted_convolution'
    else:
        return dict(common, status='OPEN', reason='no admitted full centered-prefix provider',
                    atoms=atoms, periodic_copies=periods,
                    critical_inverse_count=atoms.count({'kind': 'mu', 'shift': '0'}))
    meter.charge(10+len(stencil))
    return dict(common, status='PROVED', rule=rule, constant=str(constant), power=str(rho),
                log_power=0, subcritical=rho < F(1, 2),
                centered_at_analytic_theta_main=power_atom in atoms,
                all_subunit_arguments_retained=True)


def _pole_budget(source, j):
    orders = [sum(1 if a['kind'] == 'mu' else -1 for a in c['atoms'] if a['shift'] == 0)-j
              for c in source['channels']]
    maximum = max(orders)
    leaders = [i for i, value in enumerate(orders) if value == maximum]
    preserved = maximum > 0 and len(leaders) == 1
    return {'channel_orders': orders, 'maximum_remaining_order': maximum, 'leading_channels': leaders,
            'RH_pole_bridge_available': preserved,
            'reason': 'a reciprocal-zeta pole survives near the supremum of zero real parts' if preserved else
                      'critical inverse pole erased; this registered RH bridge is unavailable',
            'periodic_multiplier_zeros': 'Re(s)=1',
            'positive_shift_factors': 'nonzero at a zero chosen near the rightmost supremum',
            'inverse_periodic_operator_assumed_bounded': False, 'RH_proved': False}


def _program(source, family, q, j, hyperbola, scalar_bound, meter):
    channels = _transform(source, j, meter)
    prices = [_price(c, family, q, hyperbola, scalar_bound, meter) for c in channels]
    result = {'q': q, 'power': j, 'periodic': _periodic(q), 'channels': channels, 'prices': prices,
              'pole_budget': _pole_budget(source, j),
              'centering': {'theta': family['theta'], 'common_D_power': j,
                            'source_residue_zeta_multiplier': j, 'analytic_only': True,
                            'source_normalization_required': True, 'ordinary_mu_moment_assumed': False},
              'open_source_channels': [p['source_channel'] for p in prices if p['status'] == 'OPEN'],
              'uniform_complete_target_bound_proved': False, 'RH_proved': False}
    if j == 1 and result['open_source_channels'] == [family['channel_roles'][0]]:
        paid = [p for p in prices if p['status'] == 'PROVED']
        sigma = max(F(p['power']) for p in paid)
        constant = sum((F(p['constant']) for p in paid), F(0))
        beta = F(family['beta'])
        ceiling = (sigma.numerator+sigma.denominator-1)//sigma.denominator
        result['reduction'] = {
            'identity': 'prefix(A_q*f)(x)=beta*J_q(x)+R_q(x)',
            'open_source_channel': family['channel_roles'][0], 'open_weight': str(beta),
            'target': 'J_q(x)=J(x)-q*J(x/q), J(x)=prefix(K_r*mu)(x)-x^theta/(theta*zeta(theta))',
            'target_domain': 'every real x>0; centered subunit J is retained',
            'paid_remainder': {'constant': str(constant), 'power': str(sigma),
                               'domain': 'every real x>=1',
                               'energy_constant': str(constant**2*2**(2*ceiling)),
                               'energy_power': str(2*sigma-1),
                               'energy_domain': 'every integer X>=1, X^-2 sum_(X<=n<2X)',
                               'all_signed_remainder_terms_retained': True},
            'energy_implications': {
                'preconditioned_source_from_new_target': {'target_coefficient': str(2*beta**2),
                                                         'remainder_coefficient': '2'},
                'new_target_from_preconditioned_source': {'target_coefficient': str(2/beta**2),
                                                         'remainder_coefficient': str(2/beta**2)}},
            'RH_implication_requires': 'new target energy O_epsilon(X^epsilon) for EVERY epsilon>0 uniformly over X',
            'ordinary_mu_theta_series_convergence_used': False, 'inverse_A_q_bound_used': False,
            'original_F_bound_proved': False, 'new_target_bound_proved': False}
    return result


def verify(source, proposal, normalization, scalar_bound='5', meter=None):
    meter = POLE.Meter() if meter is None else meter
    family = _family(source, meter)
    bound = _fraction(scalar_bound, meter)
    _require(bound > 0, 'positive independently checked absolute scalar bound')
    _require(type(normalization) is dict and set(normalization) == {'actual_R', 'source_pole_certificate'},
             'exact normalization certificate and scalar definition')
    pole = POLE.verify(source, normalization['source_pole_certificate'],
                       actual_R=normalization['actual_R'], meter=meter)
    checks = [p for p in pole['pole_checks'] if p['point'] == family['theta']]
    _require(len(checks) == 1 and checks[0].get('exact_cancellation_proved') is True,
             'independently admitted exact source normalization, not interval-only R')
    scalar = POLE._parse_terms(normalization['actual_R'], meter)
    previous = ctx.prec
    try:
        ctx.prec = 256
        arguments = {s for key in scalar for s, exponent in key}
        values = {}
        for s in arguments:
            a = F(s)
            values[s] = (arb(a.numerator)/a.denominator).zeta()
            meter.charge(100)
            _require(values[s].is_finite() and not values[s].contains(0), 'regular scalar zeta side condition')
        value = POLE._evaluate(scalar, values, meter)
        _require(bool(abs(value) <= arb(bound.numerator)/bound.denominator),
                 'licensed uniform absolute scalar ceiling')
        scalar_interval = str(value)
    finally:
        ctx.prec = previous
    _require(type(proposal) is dict and 'q_values' in proposal and 'powers' in proposal,
             'complete periodic search proposal')
    q_values, powers = proposal['q_values'], proposal['powers']
    _require(type(q_values) is list and 1 <= len(q_values) <= 64 and
             all(type(q) is int and 2 <= q <= 4096 for q in q_values) and
             q_values == sorted(set(q_values)), 'ordered distinct bounded integer periods')
    _require(type(powers) is list and all(type(j) is int for j in powers) and powers == [0, 1, 2],
             'complete strict-integer pole-preservation/erasure audit')
    theta, v = F(family['theta']), F(family['v'])
    hyperbola = _hyperbola(theta, v, meter)
    programs = [_program(source, family, q, j, hyperbola, bound, meter) for q in q_values for j in powers]
    eligible = [p for p in programs if 'reduction' in p and p['pole_budget']['RH_pole_bridge_available'] and
                F(p['reduction']['paid_remainder']['energy_power']) < 0]
    selected = min(eligible, key=lambda p: (len(p['open_source_channels']),
                   F(p['reduction']['paid_remainder']['energy_power']), p['q'])) if eligible else None
    expected = {'schema': 'periodic-normalization-search-v1', 'source_binding': source, 'family': family,
                'q_values': q_values, 'powers': powers, 'scalar_abs_bound': scalar_bound,
                'hyperbola_search': hyperbola, 'programs': programs,
                'selected': None if selected is None else {'q': selected['q'], 'power': selected['power']},
                'selection_rule': 'preserve RH pole, require independently subcritical complete remainder, minimize open modes then remainder power then period',
                'complete_source_observations_used': False, 'normalization_premise_must_be_replayed': True,
                'uniform_complete_target_bound_proved': False, 'RH_proved': False}
    _require(POLE._same(proposal, expected), 'complete independent source, cost, pole, recovery and selection replay')
    return {'verified': True, 'normalization_exact': True, 'scalar_interval': scalar_interval,
            'scalar_abs_bound': scalar_bound, 'programs_verified': len(programs),
            'paid_reductions': len(eligible), 'selected': expected['selected'],
            'minimax_dual_weights': [str(theta/(1+theta)), str(1/(1+theta))],
            'proof_scope': {'initial_Euler_domain': pole['initial_identity_domain'],
                            'ordinary_mu_theta_convergence_asserted': False,
                            'all_shifted_divisors_and_subunit_centering_retained': True,
                            'new_linear_target_bound_proved': False,
                            'RH_bridge_requires_zeta_zero_free_line_one': True,
                            'source_normalization_is_a_separate_exact_premise': True},
            'original_F_bound_proved': False, 'uniform_complete_target_bound_proved': False,
            'RH_proved': False}
