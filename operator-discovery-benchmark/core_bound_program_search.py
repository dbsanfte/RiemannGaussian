"""Target-driven search for controls and their proof obligations.

The search receives an exponent budget, not a nominated auxiliary formula.
It enumerates polynomial combinations of complete logarithmic prefixes,
solves recovery identities, compiles derivative/projection bounds, and
works backwards to a precise remaining signed arithmetic estimate.
The primitive rules are supplied mathematics. No open leaf is a theorem.
"""
from fractions import Fraction as F
from itertools import product
from math import ceil, comb, factorial, gcd


def rational(value):
    if type(value) is not str or len(value) > 96:
        raise ValueError('bounded canonical rational string')
    q = F(value)
    if str(q) != value:
        raise ValueError('canonical rational string')
    return q


def trim(p):
    p = tuple(F(x) for x in p)
    while p and not p[-1]:
        p = p[:-1]
    return p


def at_one(p):
    """Exact coefficients of p(1-z); no numerical root detection."""
    return tuple((-1)**q * sum(p[j] * comb(j, q)
                              for j in range(q, len(p)))
                 for q in range(len(p)))


def order(p):
    return next(q for q, c in enumerate(at_one(p)) if c)


def polynomial_catalogue(spec, meter):
    degree, cap, cost = (spec[k] for k in ('degree', 'coefficient_cap', 'coefficient_l1'))
    if not (0 <= degree <= 4 and 1 <= cap <= 4 and 1 <= cost <= 16):
        raise ValueError('bounded polynomial grammar')
    result = set()
    for coefficients in product(range(-cap, cap + 1), repeat=degree + 1):
        meter.charge(10 * (degree + 1))
        if not any(coefficients) or sum(map(abs, coefficients)) > cost:
            continue
        if next(c for c in coefficients if c) < 0 or gcd(*coefficients) != 1:
            continue
        result.add(trim(coefficients))
    return sorted(result, key=lambda p: (len(p), sum(map(abs, p)), p))


def recover(polynomials, target=(F(1),)):
    """Solve sum_i a_i p_i = target by rational elimination."""
    width = len(polynomials)
    height = max(len(target), *(len(p) for p in polynomials))
    matrix = [[p[j] if j < len(p) else F(0) for p in polynomials]
              + [target[j] if j < len(target) else F(0)] for j in range(height)]
    pivots = []
    for column in range(width):
        pivot = next((j for j in range(len(pivots), height) if matrix[j][column]), None)
        if pivot is None:
            continue
        row = len(pivots)
        matrix[row], matrix[pivot] = matrix[pivot], matrix[row]
        divisor = matrix[row][column]
        matrix[row] = [v / divisor for v in matrix[row]]
        for j in range(height):
            if j != row:
                multiplier = matrix[j][column]
                matrix[j] = [v - multiplier*w for v, w in zip(matrix[j], matrix[row])]
        pivots.append(column)
    if any(not any(row[:-1]) and row[-1] for row in matrix):
        return None
    answer = [F(0)] * width
    for row, column in enumerate(pivots):
        answer[column] = matrix[row][-1]
    return tuple(answer)


def constructions(polynomials, spec, meter):
    """Backward sum/difference expansion of the recovery target 1.

    A generated p is paired with (1-a*p)/b only if that second polynomial
    is independently in the same grammar. This avoids quadratic pair scans.
    """
    allowed = set(polynomials)
    pairs = {((F(1),),)}
    multipliers = [rational(s) for s in spec['recovery_multipliers']]
    if not multipliers or any(not x for x in multipliers):
        raise ValueError('nonzero recovery multipliers')
    for p in polynomials:
        for a, b in product(multipliers, repeat=2):
            q = trim(((F(int(j == 0)) - a*c) / b) for j, c in enumerate(p))
            meter.charge(40 * len(p))
            if q in allowed and p != q:
                pair = tuple(sorted((p, q)))
                coefficients = recover(pair)
                if coefficients is not None and all(coefficients):
                    pairs.add(pair)
    return sorted(pairs, key=lambda ps: (len(ps), sum(sum(map(abs, p)) for p in ps), ps))


def moment_constant(q):
    return sum(factorial(q) // factorial(j) for j in range(q + 1))


def channel_certificate(p, eta):
    if not p or not 0 <= eta <= 4:
        raise ValueError('nonzero polynomial and nonnegative bounded rational log weight')
    b = at_one(p)
    weight = sum(map(abs, b))
    terms = []
    for q, coefficient in enumerate(b):
        if not coefficient:
            continue
        cq = moment_constant(q)
        drift = q * (moment_constant(q-1) if q else 0) + (q+eta)*cq
        constant = 2**ceil(2*(q+eta)) * (32 + 8*drift*drift)
        terms.append(dict(q=q, coefficient=str(coefficient), constant=str(constant)))
    constant = weight * sum(abs(F(t['coefficient']))*F(t['constant']) for t in terms)
    return dict(polynomial=[str(c) for c in p], eta=str(eta), vanishing_order=order(p),
                shifted_coefficients=[str(c) for c in b], terms=terms,
                derivative_constant=str(constant), derivative_log_power=str(3-2*(order(p)+eta)),
                rule='complete_prefix_jump_plus_weight_derivative', full_unit_retained=True)


def compile_program(polynomials, desired_gain, meter):
    if not 0 <= desired_gain <= 4:
        raise ValueError('nonnegative bounded log gain')
    a = recover(polynomials)
    if a is None or not all(a):
        raise ValueError('no complete nonredundant recovery')
    channels = [channel_certificate(p, max(F(0), desired_gain-order(p))) for p in polynomials]
    ell = 2*max(F(c['eta']) for c, coefficient in zip(channels, a) if coefficient)
    recovery = 2**ceil(ell)*sum(c*c for c in a)
    constant = sum(F(c['derivative_constant']) for c in channels)/8
    power = max(F(c['derivative_log_power']) for c in channels)
    meter.charge(500 * sum(len(p) for p in polynomials))
    return dict(channels=channels, recovery_coefficients=[str(c) for c in a],
                desired_gain=str(desired_gain), recovery_constant=str(recovery), recovery_log_power=str(ell),
                detail_constant_times_K_squared=str(constant), detail_log_power=str(power),
                recovered_detail_log_power=str(power+ell),
                degree=max(len(p)-1 for p in polynomials),
                cancellation_order=max(c['vanishing_order'] for c in channels),
                complexity=str(sum(sum(abs(c) for c in p) + len(p) for p in polynomials)),
                normalization_only=len(polynomials) == 1,
                proof_rules=['exact_polynomial_recovery', 'weighted_Cauchy', 'divisor_summatory',
                             'prefix_product_rule', 'orthogonal_projection_path_bound'],
                uniform_detail_bound_proved_given_majorant=True,
                uniform_coarse_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def target_branch(program, mesh_power, target_log_power, rho, meter):
    r, p, rho = map(F, (mesh_power, target_log_power, rho))
    if not (0 < r <= 1 and p >= 0 and 0 < rho <= 1):
        raise ValueError('mesh, target and recurrence domain')
    e = 2*r-1
    ell = F(program['recovery_log_power'])
    m = F(program['recovered_detail_log_power'])
    k = p-ell-int(rho == 1)
    absorption = None
    if e > 0:
        status = 'unpaid_detail_power'
    elif e == 0 and m > p:
        status = 'unpaid_recovered_detail_log'
    elif k < 0:
        status = 'requires_decaying_coarse_bound_outside_recurrence_rule'
    else:
        status = 'partial_bound_open_signed_coarse'
        if e < 0:
            t = ceil(max(F(0), m))
            absorption = F(1) if not t else 2*factorial(t)*(F(2)/(-e))**t
    meter.charge(60)
    return dict(mesh_power=str(r), target_log_power=str(p), rho=str(rho), status=status,
                detail_X_power=str(e), recovered_detail_log_power=str(m),
                detail_absorption_constant=None if absorption is None else str(absorption),
                required_coarse_forcing_log_power=str(k),
                full_bound_proved=False, open_leaf_count=1)


def open_obligation(program, branch, parent):
    if branch['status'] != 'partial_bound_open_signed_coarse':
        raise ValueError('unpaid reductions cannot be promoted')
    theta = rational(parent['transport_program']['theta'])
    if theta > F(5, 6) or parent['uniform_premise_established']:
        raise ValueError('paid transport of an unresolved source')
    return dict(schema='bound-program-obligation-v1', status='open',
        parent_obligation=parent['id'], transport_program=parent['transport_program'],
        construction=program, reduction=branch,
        definitions=dict(L='log(2n)', H_j='sum_(1<=k<=n) g(k)*log(k)^j, including k=1',
            V_i='L(n)^(-eta_i) * sum_j c_(i,j)*H_j(n)/L(n)^j',
            A='X^(-2)*sum_(X<=n<2X) sum_i V_i(n)^2',
            S='X^(-2)*sum_complete_cells |cell|*sum_i mean_cell(V_i)^2',
            cell_length='2^floor(mesh_power*log2X)', full_history=True),
        signed_source_kernel=dict(
            w_i='w_i(I,k)=mean_(n in I) [1_(k<=n)*L(n)^(-eta_i)*p_i(log(k)/L(n))]',
            J='J_X(h,k)=X^(-2)*sum_(cells I) |I|*sum_i w_i(I,h)*w_i(I,k)',
            exact_increment='sum_(1<=h,k<4X) g(h)*g(k)*(J_(2X)(h,k)-rho*J_X(h,k))',
            outside_support='J_X(h,k)=0 when h>=2X or k>=2X',
            retains=['all signed cross terms', 'full unit', 'all primes and repeated prime powers', 'complete prefix history']),
        required=dict(expression='S(2X)-rho*S(X)', rho=branch['rho'],
            upper='C*(1+log2X)^k', k=branch['required_coarse_forcing_log_power'],
            quantifier='one fixed finite C, EVERY dyadic X>=1',
            constant_fitted=False, proved=False),
        conditional_conclusion=dict(expression='E_F(X)=O((1+log2X)^target_log_power)',
            target_log_power=branch['target_log_power'],
            original_recovery='E_F<=2*C_rec*h^ell*(S+detail)+50*X^(2theta-5/3)',
            h='1+log2X', original_units_centers_and_corrections_retained=True),
        dependency_graph=[
            dict(id='signed_coarse_increment', status='open', depends_on=[]),
            dict(id='coarse_growth', status='conditional', depends_on=['signed_coarse_increment'], rule='dyadic_induction'),
            dict(id='storage_growth', status='conditional', depends_on=['coarse_growth'], rule='add_proved_detail'),
            dict(id='core_growth', status='conditional', depends_on=['storage_growth'], rule='full_energy_recovery_and_paid_transport')],
        original_fixed_constant_claim_discharged=False,
        variable_weights_commuted_through_projection=False,
        old_obligation_retained=True, whole_signed_bound_proved=False, RH_proved=False)


def priority_key(program):
    return (F(program['recovery_log_power']), F(program['complexity']),
            F(program['detail_constant_times_K_squared']),
            tuple(tuple(c['polynomial']) for c in program['channels']))


def search(spec, meter):
    polys = polynomial_catalogue(spec, meter)
    pairs = constructions(polys, spec, meter)
    programs, branches, representatives = [], [], {}
    for pair in pairs:
        for gain in spec['gains']:
            program = compile_program(pair, rational(gain), meter)
            program['id'] = len(programs)
            programs.append(program)
            for r, p, rho in product(spec['meshes'], spec['target_log_powers'], spec['rhos']):
                branch = target_branch(program, rational(r), rational(p), rational(rho), meter)
                branch['program_id'] = program['id']
                branch['id'] = len(branches)
                branches.append(branch)
                if branch['status'] != 'partial_bound_open_signed_coarse' or program['normalization_only']:
                    continue
                # Keep separate proof costs, cancellations, and fractional
                # weights. No source values or expected formula pick winners.
                key = (r, p, rho, program['cancellation_order'], gain)
                old = representatives.get(key)
                if old is None or priority_key(program) < priority_key(programs[old['program_id']]):
                    representatives[key] = branch
    # Fair bounded archive: each geometry/target/recurrence gets a turn.
    lanes = {}
    for key, branch in representatives.items():
        lanes.setdefault(key[:3], []).append(branch)
    for lane in lanes.values():
        lane.sort(key=lambda b: (F(programs[b['program_id']]['desired_gain']).denominator,
                                F(programs[b['program_id']]['desired_gain']),
                                programs[b['program_id']]['cancellation_order'],
                                priority_key(programs[b['program_id']])))
    chosen = []
    while len(chosen) < spec['archive_limit'] and any(lanes.values()):
        for key in sorted(lanes):
            if lanes[key] and len(chosen) < spec['archive_limit']:
                chosen.append(lanes[key].pop(0))
    meter.live(len(programs)*120 + len(branches)*30)
    return dict(polynomials=[[str(c) for c in p] for p in polys], constructions=len(pairs),
                programs=programs, branches=branches, selected=chosen,
                candidate_selection_uses_source_values=False,
                proof_search_model_calls=0, full_signed_bounds_proved=0)


def weak_fact_guard(program, branch):
    """A generic obstruction is separate from a counterexample to actual g."""
    return dict(status='weak_facts_cannot_close_signed_leaf',
        source='h(1)=-9; h(n)=1 for even n>=4; h(n)=0 otherwise',
        prefix='H(n)=floor(n/2)-10 >= n/4 for n>=40',
        original_energy='E_H(X)>=X/16 for all dyadic X>=64',
        storage_lower='A_h(X)>=X/(16*C_rec*(1+log2X)^ell)',
        C_rec=program['recovery_constant'], ell=program['recovery_log_power'],
        coarse_lower='S_h=A_h-detail; detail has X exponent<=0 on admitted energy branches, so S_h eventually dominates every fixed log power',
        detail_X_power=branch['detail_X_power'],
        satisfies=['coefficient divisor majorant', 'zero coefficient at every actual prime',
                   'all generated universal identities and derivative estimates'],
        full_actual_source_AST_satisfied=False, actual_core_bound_disproved=False,
        requirement_for_next_search='use complete-source signed identities in the emitted pair kernel; replaying only divisor envelopes cannot close it')


def literal_channels(g, program):
    """Small transparent finite semantics for tests/probes; no source fitting."""
    from flint import arb
    result = [[arb(0)] * len(g) for _ in program['channels']]
    for n in range(1, len(g)):
        L = arb(2*n).log()
        for i, channel in enumerate(program['channels']):
            p = list(map(F, channel['polynomial']))
            total = arb(0)
            for k in range(1, n+1):
                t = arb(k).log()/L
                v = arb(0)
                for coefficient in reversed(p):
                    v = v*t + arb(coefficient.numerator)/coefficient.denominator
                total += g[k]*v
            eta = F(channel['eta'])
            result[i][n] = total/L.root(eta.denominator)**eta.numerator
    return result
