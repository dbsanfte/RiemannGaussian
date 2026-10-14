"""Synthesize support-certified decompositions of the actual inverse factors.

The polynomial coefficients are solved from the denominator equation.
This is source-specific signed arithmetic, not a generic divisor envelope.
Every residual convolution and cross term remains in the emitted target.
"""
from fractions import Fraction as Q
from itertools import product
from math import ceil
from flint import arb

CUTOFFS = ('1/6', '1/3', '1/2', '2/3', '5/6')


def rational(s):
    if type(s) is not str or len(s) > 128:
        raise ValueError('bounded canonical rational')
    q = Q(s)
    if str(q) != s:
        raise ValueError('canonical rational')
    return q


def multiply(a, b, meter):
    result = {}
    for (i, j), x in a.items():
        for (k, l), y in b.items():
            key = (i+k, j+l)
            result[key] = result.get(key, Q(0))+x*y
            meter.charge(8)
    return {key: value for key, value in result.items() if value}


def synthesize(alpha, gamma, p, q, meter):
    a, b = rational(alpha), rational(gamma)
    if not (0 < a < 1 and 0 < b < 1 and type(p) is int and type(q) is int
            and 0 <= p <= 2 and 0 <= q <= 2 and p+q):
        raise ValueError('finite short-inverse grammar')
    denominator = {(0, 0): Q(1)}
    for _ in range(p):
        denominator = multiply(denominator, {(0, 0): Q(1), (1, 0): Q(-1)}, meter)
    for _ in range(q):
        denominator = multiply(denominator, {(0, 0): Q(1), (0, 1): Q(-1)}, meter)
    region = sorted(((i, j) for i in range(ceil(1/a)) for j in range(ceil(1/b)) if a*i+b*j < 1),
                    key=lambda ij: (sum(ij), ij))
    solution = {}
    for i, j in region:
        value = Q(int(i == 0 and j == 0))
        for (k, l), c in denominator.items():
            if k+l and k <= i and l <= j:
                value -= c*solution.get((i-k, j-l), Q(0))
                meter.charge(10)
        if value:
            solution[(i, j)] = value
    return dict(alpha=alpha, gamma=gamma, p=p, q=q,
                terms=[dict(a=i, b=j, coefficient=str(solution[(i, j)])) for i, j in region if (i, j) in solution])


def decode_source(source):
    """Read all four complete zeta-factor rows; do not nominate their expansion."""
    modes = []
    for term in source['terms']:
        mode = dict(name=term['name'], coefficient=term['coefficient'], p=0, q=0, positive_shift=None)
        for shift, exponent in term['zeta_factors']:
            s, e = rational(shift), rational(exponent)
            if e < 0 and e.denominator == 1 and -e <= 2 and s in (0, Q(2, 3)):
                mode['p' if s == 0 else 'q'] += int(-e)
            elif e == 1 and s == Q(1, 3) and mode['positive_shift'] is None:
                mode['positive_shift'] = str(s)
            else:
                raise ValueError('unsupported source factor; no term may be dropped')
        if not mode['p']+mode['q'] or mode['coefficient'] not in ('beta', '-beta', '-R_u'):
            raise ValueError('bound complete signed inverse mode')
        modes.append(mode)
    if len(modes) != 4 or len({m['name'] for m in modes}) != 4:
        raise ValueError('complete four-mode source')
    return modes


def catalogue(source, meter):
    modes = decode_source(source)
    rows = []
    for alpha, gamma in product(CUTOFFS, repeat=2):
        cases = []
        for mode in modes:
            program = synthesize(alpha, gamma, mode['p'], mode['q'], meter)
            cases.append(dict(mode=mode, program=program))
        terms = sum(len(case['program']['terms']) for case in cases)
        depth = max(case['mode']['p']+case['mode']['q']+t['a']+t['b']+int(case['mode']['positive_shift'] is not None)
                    for case in cases for t in case['program']['terms'])
        rows.append(dict(id=len(rows), alpha=alpha, gamma=gamma, cases=cases,
                         component_count=terms, maximum_convolution_factors=depth,
                         coefficient_l1=str(sum(abs(Q(t['coefficient'])) for case in cases for t in case['program']['terms'])),
                         identity_scope='EVERY integer N>=1, EVERY n<=N; cutoffs floor(N^alpha),floor(N^gamma)',
                         uniform_signed_bound_proved=False))
    return rows


def select(rows):
    chosen = {}
    for budget in (4, 5, 8):
        eligible = [r for r in rows if r['maximum_convolution_factors'] <= budget]
        if not eligible:
            continue
        for lane in ('balanced_short_factors', 'short_unshifted_inverse'):
            def key(r):
                a, b = Q(r['alpha']), Q(r['gamma'])
                return ((max(a, b), a+b, r['component_count'], a, b) if lane == 'balanced_short_factors'
                        else (a, r['component_count'], Q(r['coefficient_l1']), b))
            row = min(eligible, key=key)
            chosen.setdefault(row['id'], dict(row, selection_routes=[]))['selection_routes'].append(dict(lane=lane, factor_budget=budget))
    return list(chosen.values())


def cutoff(N, exponent):
    q = rational(exponent)
    if type(N) is not int or N < 1 or not 0 < q < 1:
        raise ValueError('positive horizon and strict fractional cutoff')
    target = N**q.numerator
    low, high = 0, N+1
    while low+1 < high:
        middle = (low+high)//2
        if middle**q.denominator <= target:
            low = middle
        else:
            high = middle
    return low


def convolve(a, b, meter):
    if len(a) != len(b) or not a[0].is_zero() or not b[0].is_zero():
        raise ValueError('complete common support and dummy zero')
    H = len(a)-1
    result = [arb(0)]*(H+1)
    # Sparse first-factor iteration avoids long arrays of known zeros.
    for d in range(1, H+1):
        if a[d].is_zero():
            continue
        for k in range(1, H//d+1):
            result[d*k] += a[d]*b[k]
            meter.charge(8)
    return result


def evaluate(mu, program, H, meter):
    if len(mu) != H+1 or mu[0] != 0 or mu[1] != 1 or any(type(v) is not int or v not in (-1, 0, 1) for v in mu):
        raise ValueError('complete actual Mobius input including unit')
    U, V = cutoff(H, program['alpha']), cutoff(H, program['gamma'])
    one = [arb(0)]+[arb(1)]*H
    twist = [arb(0)]+[1/arb(n).root(3)**2 for n in range(1, H+1)]
    unit = [arb(0)]*(H+1)
    unit[1] = arb(1)
    A = [arb(0)]+[arb(mu[n] if n <= U else 0) for n in range(1, H+1)]
    B = [arb(0)]+[mu[n]*twist[n] if n <= V else arb(0) for n in range(1, H+1)]
    R = [x-y for x, y in zip(unit, convolve(one, A, meter))]
    S = [x-y for x, y in zip(unit, convolve(twist, B, meter))]
    # S(n)=n^(-2/3) sum_{d|n}(delta(d)-mu(d)1_(d<=V)).
    # This exact twist identity removes interval dependency at support zeros.
    integer_residual = [0]*(H+1)
    integer_residual[1] = 1
    for d in range(1, V+1):
        for n in range(d, H+1, d):
            integer_residual[n] -= mu[d]
            meter.charge(2)
    for n in range(H+1):
        exact = integer_residual[n]*twist[n]
        if not exact.overlaps(S[n]):
            raise ArithmeticError('twisted residual identity')
        S[n] = exact
    for n in range(1, U+1):
        if not R[n].is_zero():
            raise ValueError('mu inverse support premise')
    for n in range(1, V+1):
        if not S[n].is_zero():
            raise ValueError('shifted inverse support premise')
    prefactor = unit
    for factor, power in ((A, program['p']), (B, program['q'])):
        for _ in range(power):
            prefactor = convolve(prefactor, factor, meter)
    rpow, spow = [unit], [unit]
    for _ in range(max(t['a'] for t in program['terms'])):
        rpow.append(convolve(rpow[-1], R, meter))
    for _ in range(max(t['b'] for t in program['terms'])):
        spow.append(convolve(spow[-1], S, meter))
    terms, reconstructed = [], [arb(0)]*(H+1)
    for term in program['terms']:
        value = prefactor
        if term['a']:
            value = convolve(value, rpow[term['a']], meter)
        if term['b']:
            value = convolve(value, spow[term['b']], meter)
        coefficient = Q(term['coefficient'])
        c = arb(coefficient.numerator)/coefficient.denominator
        reconstructed = [x+c*y for x, y in zip(reconstructed, value)]
        terms.append(dict(term, values=value))
        meter.charge(5*(H+1))
    meter.live((12+len(rpow)+len(spow)+len(terms))*(H+1))
    return dict(H=H, U=U, V=V, A=A, B=B, R=R, S=S, terms=terms, reconstructed=reconstructed)


def source_components(mu, row, source_scalars, H, meter, evaluator=evaluate):
    ku = [arb(0)]+[1/arb(n).root(3) for n in range(1, H+1)]
    components, cases = [], []
    full = [arb(0)]*(H+1)
    for case in row['cases']:
        value = evaluator(mu, case['program'], H, meter)
        mode = case['mode']
        c_mode = source_scalars[mode['coefficient']]
        restored = [arb(0)]*(H+1)
        for term in value['terms']:
            v = convolve(ku, term['values'], meter) if mode['positive_shift'] else term['values']
            c = Q(term['coefficient'])
            c_full = c_mode*arb(c.numerator)/c.denominator
            signed = [c_full*x for x in v]
            restored = [x+y for x, y in zip(restored, signed)]
            components.append(dict(mode=mode['name'], a=term['a'], b=term['b'], coefficient=str(c_full), values=signed))
            meter.charge(5*(H+1))
        full = [x+y for x, y in zip(full, restored)]
        cases.append(dict(mode=mode['name'], program=case['program'], U=value['U'], V=value['V'],
                          restored=restored, inverse=value))
    return dict(H=H, geometry=row['id'], components=components, cases=cases, restored_source=full)


def absolute_factor_obstruction():
    return dict(status='absolute_factor_route_cannot_pay_core_exponent',
        term='beta*k_(1/3)*A*A from the constant monomial of the first complete source mode',
        reason='|A|(1)=1 forces |A|*|A|*k_(1/3) >= k_(1/3) pointwise',
        prefix_lower='for n>=1, sum_(k<=n)k^(-1/3)>=n^(2/3)',
        energy_lower='unsigned factorwise prefix energy on[X,2X) >= beta^2*X^(1/3)',
        discarded_X_power='1/3', scope='only the fully unsigned factorwise majorant; not signed component energy or the complete joined source',
        actual_core_bound_disproved=False, signed_component_route_disproved=False,
        required_next_step='bound the joined signed short-factor/residual correlations, retaining every cross term')


def component_bounds(row, meter):
    """Search competing valid critical-l1 rules, then compose exact costs."""
    alpha, gamma = Q(row['alpha']), Q(row['gamma'])
    # (constant, N-power, log degree, rule). Norm uses sum |h(n)|/sqrt(n).
    rules = dict(A=[(Q(2), alpha/2, 0, 'finite_Mobius_cutoff')],
                 B=[(Q(7), Q(0), 0, 'summable_shifted_cutoff')],
                 R=[(Q(5), (1+alpha)/2, 0, 'direct_inverse_residual'),
                    (Q(2), Q(1, 2), 1, 'actual_Mobius_tail_identity')],
                 S=[(Q(50), Q(0), 0, 'direct_shifted_residual'),
                    (Q(84), -gamma/6, 0, 'actual_shifted_tail_identity')])
    selected = {key: min(values, key=lambda v: (v[1], v[2], v[0])) for key, values in rules.items()}
    output = []
    for case in row['cases']:
        mode = case['mode']
        for t in case['program']['terms']:
            scalar = Q(5) if mode['coefficient'] == '-R_u' else Q(9, 2)
            constant = abs(Q(t['coefficient']))*scalar
            exponent, log_degree = Q(0), 0
            if mode['positive_shift']:
                constant *= 6
                exponent += Q(1, 6)
            used = []
            for factor, count in (('A', mode['p']), ('B', mode['q']), ('R', t['a']), ('S', t['b'])):
                c, e, k, rule = selected[factor]
                constant *= c**count
                exponent += count*e
                log_degree += count*k
                if count:
                    used.append(dict(factor=factor, power=count, rule=rule))
            # A second proof route preserves the finite l1 size and the
            # 1/X block normalization. Critical weighted l1 alone loses
            # this gain for a genuinely short component such as A.
            epsilon = int(mode['positive_shift'] is not None)
            ordinary_c = abs(Q(t['coefficient']))*scalar*Q(3,2)**epsilon*3**(mode['q']+t['b'])
            ordinary_e = Q(2,3)*epsilon+mode['p']*alpha+mode['q']*gamma/3+t['a']+Q(t['b'],3)
            ordinary_log = t['a']+t['b']
            alternatives = [dict(rule='critical_weighted_l1', constant=str(4*constant*constant),
                                 power=str(2*exponent), log_degree=2*log_degree),
                            dict(rule='ordinary_l1_and_block_normalization', constant=str(4*ordinary_c*ordinary_c),
                                 power=str(2*ordinary_e-1), log_degree=2*ordinary_log)]
            best = min(alternatives, key=lambda r: (Q(r['power']), r['log_degree'], Q(r['constant'])))
            output.append(dict(mode=mode['name'], a=t['a'], b=t['b'],
                critical_mass_constant=str(constant), critical_mass_N_power=str(exponent),
                critical_mass_log_degree=log_degree,
                energy_constant=best['constant'], energy_N_power=best['power'], energy_log_degree=best['log_degree'],
                energy_rule=best['rule'], energy_alternatives=alternatives,
                mass_definition='sum_(n<=N)|h(n)|/sqrt(n)',
                energy_domain='complete prefix energy at X and2X, common N=4X-1',
                chosen_rules=used, cofinally_paid_by_this_rule=Q(best['power']) <= 0,
                signed_component_bound_disproved=False))
            meter.charge(200)
    return dict(components=output,
                rules={key:[dict(constant=str(c), power=str(e), log_degree=k, rule=r) for c,e,k,r in values]
                       for key,values in rules.items()},
                componentwise_route_closes_target=all(t['cofinally_paid_by_this_rule'] for t in output),
                preserves_possibility_of_joined_signed_control=True)


def centered_residual(mu, U, residual, meter):
    """Infer and verify the unique affine slope of the truncated divisor sum.

    R_prefix(n)=1-sum_(d<=U)mu(d)*floor(n/d).
    Replacing floor(n/d) by n/d determines its slope by exact arithmetic.
    Adding c_U*One to R leaves prefix 1+sum mu(d)*frac(n/d), uniformly
    bounded by 1+sum|mu(d)|. The compensating drift is retained explicitly.
    """
    if not 1 <= U < len(mu) or len(mu) != len(residual):
        raise ValueError('complete truncated inverse support')
    c = sum((Q(mu[d], d) for d in range(1, U+1)), Q(0))
    constant = 1+sum(abs(mu[d]) for d in range(1, U+1))
    rc = arb(c.numerator)/c.denominator
    values = [arb(0)]+[v+rc for v in residual[1:]]
    prefix, checks = arb(0), 0
    for n in range(1, len(values)):
        prefix += values[n]
        exact = Q(1)+sum((Q(mu[d]*(n%d), d) for d in range(1, min(n, U)+1)), Q(0))
        # d>n still contributes mu(d)*n/d; it may not be removed from the
        # full fixed-U centering sum or from the exact compensating slope.
        exact += sum((Q(mu[d]*n, d) for d in range(n+1, U+1)), Q(0))
        ball = arb(exact.numerator)/exact.denominator
        if not prefix.overlaps(ball) or abs(exact) > constant:
            raise ArithmeticError('complete centered floor remainder')
        meter.charge(15*U+10)
        checks += 1
    return dict(cutoff=U, exact_slope=str(c), prefix_bound=constant,
        values=values, identity_checks=checks,
        full_identity='R=E_U-c_U*One; no drift term is discarded',
        uniform_prefix_formula='sum_(k<=n)E_U(k)=1+sum_(d<=U)mu(d)*(n mod d)/d for every n>=1',
        uniform_bound='|prefix E_U|<=1+sum_(d<=U)|mu(d)|<=1+U for EVERY n>=1',
        drift_constant_known_exactly=True, original_residual_bound_proved=False)


def primitive_controls(row):
    alpha, gamma = Q(row['alpha']), Q(row['gamma'])
    return dict(
        shifted_residual=dict(status='proved', norm='sum_(n>=1)|S(n)|/sqrt(n)',
            bound='42*V^(-1/6)<=84*N^(-gamma/6)', N_power=str(-gamma/6),
            inverse_identity_required=True, infinite_tail_included=True,
            half_contraction_sufficient_cutoff=84**6),
        centered_unshifted_residual=dict(status='proved', definition='E_U=R+c_U*One, c_U=sum_(d<=U)mu(d)/d',
            prefix_bound='1+U for every integer n>=1',
            energy_bound='E_(prefix E_U)(X)<=16*N^(2alpha-1), N=4X-1',
            energy_N_power=str(2*alpha-1), cofinally_paid=alpha <= Q(1,2),
            drift='-c_U*One retained exactly', drift_energy_upper='4*c_U^2*X',
            uncentered_residual_bound_proved=False),
        full_signed_core_bound_proved=False)


def paid_component_reduction(parent, row, bounds):
    paid = [b for b in bounds['components'] if b['cofinally_paid_by_this_rule']]
    if any(b['energy_log_degree'] for b in paid):
        raise ValueError('this reduction expects uniformly bounded paid pieces')
    C_channel = sum((2**ceil(Q(c['eta']))*sum(abs(Q(v)) for v in c['polynomial']))**2
                    for c in parent['construction']['channels'])
    C_paid = len(paid)*C_channel*sum(Q(b['energy_constant']) for b in paid)
    original = parent['reduction']
    growth_degree = Q(original['required_coarse_forcing_log_power'])+int(Q(original['rho']) == 1)
    return dict(paid_components=[dict(mode=b['mode'], a=b['a'], b=b['b']) for b in paid],
        channel_majorant_constant=str(C_channel), combined_paid_coarse_constant=str(C_paid),
        exact_split='full channel vector = joined remaining vector Z + paid vector P',
        global_recovery='S_full<=2*S_Z+2*C_paid, S_Z<=2*S_full+2*C_paid at every dyadicX',
        source_horizon='N=4X-1 for the entire decomposition; transport error stays in Z',
        new_sufficient_goal=dict(expression='S_Z(X)<=C*(1+log2X)^p for EVERY dyadicX>=1',
            p=str(growth_degree), status='open', same_finite_constant=True),
        older_fixed_recurrence_discharged=False, full_unit_accounted_for_in_paid_vector=True,
        remaining_crosses_preserved=True, whole_signed_bound_proved=False)


def projected_means(values, program, X, mesh_power, meter, method='prefix'):
    """Two linear evaluations of complete channel means; no source refit.

    The Abel route takes full right-endpoint prefixes and subtracts every
    internal coefficient's accumulated weight. The prefix route weights
    each prefix directly. Both retain the entire history before a cell.
    """
    r = rational(mesh_power)
    if type(X) is not int or X < 1 or X & (X-1) or len(values) < 2*X or not 0 < r <= 1:
        raise ValueError('complete dyadic projection')
    if method not in ('prefix', 'abel'):
        raise ValueError('declared independent mean algorithm')
    L = 1 << (r.numerator*(X.bit_length()-1)//r.denominator)
    degree = max(len(c['polynomial'])-1 for c in program['channels'])
    logs = [arb(0)]+[arb(n).log() for n in range(1, 2*X)]
    banks = [[arb(0)]*(2*X) for _ in range(degree+1)]
    increments = [[arb(0)]*(2*X) for _ in range(degree+1)]
    for n in range(1, 2*X):
        for j in range(degree+1):
            increments[j][n] = values[n]*logs[n]**j
            banks[j][n] = banks[j][n-1]+increments[j][n]
            meter.charge(20)
    result = []
    for lo in range(X, 2*X, L):
        hi = lo+L
        channels = []
        for channel in program['channels']:
            eta = Q(channel['eta'])
            mean = arb(0)
            for j, text in enumerate(channel['polynomial']):
                c = Q(text)
                if not c:
                    continue
                weights = [1/(arb(2*n).log().root(eta.denominator)**eta.numerator*arb(2*n).log()**j)
                           for n in range(lo, hi)]
                if method == 'prefix':
                    value = sum((banks[j][n]*weights[n-lo] for n in range(lo, hi)), arb(0))
                else:
                    total_weight = arb(0)
                    internal = arb(0)
                    for n in range(lo, hi):
                        internal += increments[j][n]*total_weight
                        total_weight += weights[n-lo]
                    value = banks[j][hi-1]*total_weight-internal
                mean += (arb(c.numerator)/c.denominator)*value/L
                meter.charge(150*L)
            channels.append(mean)
        result.append(dict(start=lo, stop=hi, means=channels))
    return result


def joined_projection(components, error_component, direct_g, program, X, mesh_power, meter, method='prefix'):
    means = [projected_means(c['values'], program, X, mesh_power, meter, method) for c in components]
    means.append(projected_means(error_component, program, X, mesh_power, meter, method))
    direct = projected_means(direct_g, program, X, mesh_power, meter, method)
    diagonal = cross = whole = arb(0)
    cells = []
    for index, cell in enumerate(direct):
        length = cell['stop']-cell['start']
        joint_means = []
        for channel in range(len(program['channels'])):
            total = arb(0)
            for component in means:
                v = component[index]['means'][channel]
                diagonal += length*v*v
                cross += 2*length*total*v
                total += v
                meter.charge(20)
            if not total.overlaps(cell['means'][channel]):
                raise ArithmeticError('full signed component mean failed to recover actual g')
            whole += length*total*total
            joint_means.append(total)
        cells.append(dict(start=cell['start'], stop=cell['stop'], joined=joint_means, direct=cell['means']))
    if not (whole-diagonal-cross).contains(0):
        raise ArithmeticError('complete signed cross identity')
    return dict(X=X, mesh_power=mesh_power, cells=cells,
                full_coarse=whole/(X*X), component_diagonal=diagonal/(X*X),
                complete_signed_cross=cross/(X*X), all_components_including_transport_error=len(means),
                no_triangle_inequality_applied=True, uniform_bound_proved=False)


def obligation(parent, row):
    return dict(schema='actual-source-truncated-inverse-obligation-v1', status='open',
        parent_obligation_id=parent['id'], parent_required_bound=parent['required'],
        source_geometry=dict(alpha=row['alpha'], gamma=row['gamma'], cases=row['cases']),
        horizon='N=4X-1 for BOTH S(2X) and S(X) in the entire increment',
        actual_inverse_inputs=['mu*One=delta on all positive integers', '(mu*n^(-2/3))*(n^(-2/3))=delta'],
        source_reconstruction='f=sum_t c_t h_t, g=sum_t c_t h_t-e, e=f-g from the SAME transport',
        component_definition='h_t=k_positive*A^(*p)*B^(*q)*R^(*a)*S^(*b); omit k_positive if absent',
        full_joined_target='sum_(t,u) c_t*c_u <T(h_t),T(h_u)>_(child-rho*parent), including exact transport-error component',
        T=parent['definitions'], signed_kernel=parent['signed_source_kernel'],
        no_component_triangle_inequality_applied=True,
        newly_available_primitive_controls=primitive_controls(row),
        centered_expansion_rule='Only AFTER support truncation, substitute R=E_U-c_U*One and retain every binomial/drift cross; E_U has NO cutoff support gap',
        uniform_identity_proved=True, uniform_required_inequality_proved=False,
        factorwise_absolute_obstruction=absolute_factor_obstruction(),
        all_units_primes_valuations_and_histories_retained=True,
        source_scale_dependence_is_only_exact_decomposition=True,
        whole_signed_bound_proved=False, RH_proved=False)
