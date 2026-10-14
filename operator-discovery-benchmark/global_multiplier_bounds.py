"""Search complete all-N source relations for rational quadratic bounds.

Unknown multipliers are solved from the proposed form. Every auxiliary retains
its original-source meaning, forcing prices, and any missing energy theorem.
The search uses no observed arithmetic coefficients or numerical fits.
"""
from copy import deepcopy
from fractions import Fraction as Q
from itertools import product

import sympy as S

import arithmetic_prefix_relations as A
import global_multiplier_proto_039 as M


def join_relation(source, certificate, meter):
    A.validate_source(source, meter)
    if certificate != A.generate(source, meter):
        raise ValueError('source-generated complete relation certificate')
    grouped = {}
    for row in certificate['relations']:
        key = tuple(f['exponent'] for f in row['rhs']['factors'])
        weight = [Q(x) for x in row['weight']]
        previous = grouped.setdefault(key, [Q(0), Q(0)])
        for i in range(2):
            previous[i] -= weight[i]
    return dict(source_binding=deepcopy(source),
        target='complete original prefix F(n)=sum_j W_j(n)',
        tail='T(n)=sum_j sum_(2<=d<=n)D_j(d)*W_j(floor(n/d))',
        forcing=[dict(power_factors=list(key), weight=list(map(str, weight)))
                 for key, weight in sorted(grouped.items()) if any(weight)],
        identity='F+T+sum forcing=0', domain='every integer n>=1',
        all_floor_terms_and_source_channels=True, tail_status='OPEN')


def rhs_price(rhs, interval=('1', '5')):
    """Elementary all-integer block prices; power/log cost is part of admission."""
    a, b = map(Q, rhs['weight']); low, high = map(Q, interval)
    if low > high:
        raise ValueError('ordered scalar interval')
    ceiling = max(abs(a+b*low), abs(a+b*high))
    powers = list(map(Q, rhs['power_factors']))
    common = dict(rhs=deepcopy(rhs), R_interval=list(interval),
                  weight_ceiling=str(ceiling),
                  norm='X^-2 sum_(X<=n<2X) value(n)^2',
                  domain='every integer X>=1')
    if not powers:
        rule, constant, exponent, logs = 'delta_prefix', ceiling**2, Q(-1), 0
    elif len(powers) > 1:
        return dict(**common, status='OPEN', reason='multiple power factors have no admitted price')
    else:
        e = powers[0]
        if e < -1:
            rule = 'convergent_power_integral'
            constant, exponent, logs = ceiling**2*(1+1/(-e-1))**2, Q(-1), 0
        elif e == -1:
            rule = 'harmonic_integral'
            constant, exponent, logs = 4*ceiling**2, Q(-1), 2
        else:
            growth = 1+e
            ceil_growth = -((-growth.numerator)//growth.denominator)
            point_constant = 1/growth if e < 0 else Q(1)
            rule = 'decreasing_power_integral' if e < 0 else 'increasing_power_envelope'
            constant = ceiling**2*point_constant**2*2**(2*ceil_growth)
            exponent, logs = 2*growth-1, 0
    return dict(**common, status='PROVED', rule=rule,
                energy=dict(constant=str(constant), power=str(exponent), log_power=logs),
                subpower_eligible=exponent <= 0)


def basis_vector(size, index):
    return ['1' if i == index else '0' for i in range(size)]


def outer(vector):
    return [[str(Q(x)*Q(y)) for y in vector] for x in vector]


def span_obstruction(target, relations, providers, meter):
    """A vector annihilating every provider excludes all nonnegative weights.

    This is an exact witness only for this relation/template relaxation.
    """
    rows = relations + [p['vector'] for p in providers]
    m = S.Matrix([[S.Rational(x) for x in row] for row in rows])
    t = S.Matrix([[S.Rational(x) for x in target]])
    meter.charge(100*(len(target)+1)**3)
    for v in m.nullspace():
        if (t*v)[0]:
            v = v/(t*v)[0]
            return dict(vector=[str(x) for x in v], target_value='1',
                        all_provider_values='0', relation_values='0',
                        scope='this finite relation/template relaxation',
                        excludes_all_nonnegative_forcing_weights=True,
                        actual_arithmetic_counterexample=False)
    return None


def equivalence(target, auxiliary, relations, paid, meter):
    """Detect auxiliary = a*target + paid prefixes modulo complete relations."""
    rows = [target] + [p['vector'] for p in paid] + relations
    matrix = S.Matrix([[S.Rational(x) for x in row] for row in rows]).T
    vector = S.Matrix([S.Rational(x) for x in auxiliary])
    meter.charge(100*(len(target)+1)**3)
    try:
        answer, parameters = matrix.gauss_jordan_solve(vector)
    except ValueError:
        return None
    if parameters.rows:
        answer = answer.subs({p: 0 for p in parameters})
    if not answer[0]:
        return None
    return dict(auxiliary=auxiliary, target_coefficient=str(answer[0]),
                paid_coefficients=[str(x) for x in answer[1:1+len(paid)]],
                relation_coefficients=[str(x) for x in answer[1+len(paid):]],
                paid_ids=[p['id'] for p in paid],
                status='equivalent_subpower_obligation',
                new_bound_proved=False)


def search_case(name, target, relations, providers, meter, grid=('0', '1', '2', '4')):
    obstruction = span_obstruction(target, relations, providers, meter)
    common = dict(name=name, target=target, relations=relations,
                  providers=deepcopy(providers), coefficient_grid=list(grid),
                  whole_signed_bound_proved=False, RH_proved=False)
    if obstruction is not None:
        return dict(**common, status='no_bound_in_provider_span',
                    obstruction=obstruction, coefficient_trials=0)
    raw = M.search_forcing(target, relations,
        [dict(name=p['id'], form=outer(p['vector']), paid=p['price']['status']=='PROVED')
         for p in providers], grid=grid, meter=meter)
    result = dict(**common, status=raw['status'], search=raw,
                  coefficient_trials=len(raw['attempts']))
    if 'certificate' in raw:
        active = [p for c, p in zip(raw['coefficients'], providers) if Q(c)]
        result['open_providers'] = [p['id'] for p in active if p['price']['status'] != 'PROVED']
        result['excess_growth_providers'] = [p['id'] for p in active
            if p['price']['status']=='PROVED' and not p['price']['subpower_eligible']]
        result['meets_subpower_target'] = not (result['open_providers'] or result['excess_growth_providers'])
        result['status'] = ('conditional_energy_implication' if result['open_providers'] else
                            'proved_bound_with_excess_growth' if result['excess_growth_providers'] else
                            'proved_subpower_bound_for_case_target')
    return result


def rational_offsets(max_denominator=9, additional_denominators=(17, 257)):
    """Bound work, not semantic root orders; callers can extend the schedule."""
    values = {Q(0), Q(1), Q(2)}
    for d in range(2, max_denominator+1):
        values.update((Q(1, d), Q(d-1, d), Q(d+1, d)))
    for d in additional_denominators:
        if type(d) is not int or d < 1:
            raise ValueError('positive rational denominator')
        values.update((Q(1, d), Q(d-1, d), Q(d+1, d)))
    return [str(x) for x in sorted(values)]


def search(source, relations_certificate, meter):
    joined = join_relation(source, relations_certificate, meter)
    dim = 2+len(joined['forcing'])
    if not 2 <= dim <= 5:
        raise ValueError('bounded source-generated joined forcing coordinates')
    target = basis_vector(dim, 0); tail = basis_vector(dim, 1)
    L = [['1']*dim]
    forcing = [dict(id='rhs_'+str(i), vector=basis_vector(dim, i+2), price=rhs_price(rhs))
               for i, rhs in enumerate(joined['forcing'])]
    paid = [p for p in forcing if p['price']['status']=='PROVED' and p['price']['subpower_eligible']]
    tail_provider = dict(id='complete_joined_tail', vector=tail,
                         price=dict(status='OPEN', meaning=joined['tail']))
    cases = [search_case('critical_paid_forcing', target, L, paid, meter),
             search_case('all_rhs_paid_but_growth_charged', target, L, forcing, meter),
             search_case('complete_tail_explicitly_unpaid', target, L, forcing+[tail_provider], meter)]
    auxiliary_cases = []
    for provider in forcing:
        # Search mixing the complete tail with EACH actual RHS term, no selected winner.
        for value in rational_offsets():
            lam = Q(value)
            vector = [str(Q(x)+lam*Q(y)) for x, y in zip(tail, provider['vector'])]
            auxiliary = dict(id='tail_plus_'+value+'_'+provider['id'], vector=vector,
                price=dict(status='OPEN', construction=dict(tail='complete_joined_tail',
                    rhs_id=provider['id'], coefficient=value)))
            case = search_case(auxiliary['id'], target, L, paid+[auxiliary], meter)
            case['construction'] = auxiliary['price']['construction']
            case['equivalent_obligation'] = equivalence(target, vector, L, paid, meter)
            auxiliary_cases.append(case)
    calibrations = []
    for row in relations_certificate['relations']:
        rhs = dict(power_factors=[f['exponent'] for f in row['rhs']['factors']], weight=row['weight'])
        provider = dict(id='channel_rhs_'+str(row['channel']), vector=['0', '1'], price=rhs_price(rhs))
        trial = search_case('complete_convolved_channel_'+str(row['channel']),
                            ['1', '0'], [['1', '-1']], [provider], meter)
        trial.update(channel=row['channel'], target_kind='complete convolved prefix, not original F',
                     calibration_only=True)
        calibrations.append(trial)
    stencils = [[[1, '1']], [[1, '1'], [2, '-1']],
                [[1, '1'], [2, '-1/2'], [3, '1/257']]]
    floor_templates = []
    for row, stencil in product(relations_certificate['relations'], stencils):
        template = M.multiply_complete_relation(source, relations_certificate, row['channel'], stencil, meter)
        floor_templates.append(dict(template=template,
            split=M.complete_split(template, 3, meter),
            finite_inverse=M.finite_inverse_gate(row['kernel'], stencil, meter)))
    return dict(schema='complete-source-global-multiplier-search-v1',
        source_binding=deepcopy(source), joined_relation=joined,
        coordinate_order=['complete_original_prefix_F', 'complete_joined_tail_T']+
                         [p['id'] for p in forcing],
        source_parameter_requirement='fixed exact R, replayed separately by normalization guard',
        norm='X^-2 sum_(X<=n<2X) coordinate(n)^2, every integer X>=1',
        cases=cases, auxiliary_cases=auxiliary_cases, calibrations=calibrations,
        floor_templates=floor_templates, rational_auxiliary_coefficients=rational_offsets(),
        source_observations_used=False, whole_signed_bound_proved=False, RH_proved=False,
        limitation='scalar full-tail relaxation does not yet exploit a finite consequence of exact R')
