"""Synthesize exact recovery-bound reductions from generated frame programs.

Arithmetic lower bounds remain open. A separate exact audit detects when
the weighted residual still contains the entire original common mode.
"""
from fractions import Fraction as Q
from itertools import combinations
import core_cutoff_frame as FRAME


def decode(poly):
    return {tuple(t['monomial']): Q(t['coefficient']) for t in poly}


def scale(poly, factor):
    return {k: v*factor for k, v in poly.items() if v*factor}


def leading(poly, dimension):
    return max(poly, key=lambda m: (len(m), tuple(m.count(i) for i in range(dimension))))


def division(numerator, denominator, dimension, meter):
    """Single-divisor exact multivariate division, graded lexicographic order."""
    if not denominator:
        raise ValueError('nonzero polynomial denominator')
    residual, quotient, remainder = dict(numerator), {}, {}
    lead = leading(denominator, dimension)
    lead_counts = [lead.count(i) for i in range(dimension)]
    while residual:
        top = leading(residual, dimension)
        counts = [top.count(i)-lead_counts[i] for i in range(dimension)]
        if any(c < 0 for c in counts):
            remainder[top] = residual.pop(top)
        else:
            monomial = tuple(i for i, count in enumerate(counts) for _ in range(count))
            coefficient = residual[top]/denominator[lead]
            quotient = FRAME.add(quotient, {monomial: coefficient})
            residual = FRAME.add(residual, scale(FRAME.mul({monomial: coefficient}, denominator, meter), -1))
        meter.charge(100+20*len(residual))
    return quotient, remainder


def value(poly, variables, meter):
    total = Q(0)
    for monomial, coefficient in poly.items():
        term = coefficient
        for i in monomial:
            term *= variables[i]
        total += term
        meter.charge(10+10*len(monomial))
    return total


def condition(S, B):
    return dict(positive_denominator=FRAME.encode(S), left=FRAME.encode(S), right_factor=FRAME.encode(B),
        rho='c*(1+log2X)^(-q)', parameters='one fixed c>0, one fixed q>=0, one fixed finite dyadic X0',
        quantifier='EVERY dyadic X>=X0, N=4X-1', required='S>0 and S>=rho*B',
        conclusion='K<=c^(-1)*(1+log2X)^q', status='open')


def synthesize(catalogue, meter):
    dimension = catalogue['dimension']
    basis = [([FRAME.linear(row) for row in item['vector']], FRAME.linear(item['sum'])) for item in catalogue['basis']]
    certificates = []
    for candidate in catalogue['candidates']:
        S = decode(candidate['normalizer'])
        W = list(map(decode, candidate['weights']))
        P = {}
        for w in W:
            P = FRAME.add(P, FRAME.mul(w, w, meter))
        quotient, remainder = division(P, S, dimension, meter)
        witnesses = []
        if not remainder:
            branch, B = 'exact_quotient', quotient
        else:
            branch, B = 'cauchy_quotient', {}
            chosen = candidate['basis_ids']
            for j in chosen:
                for v in basis[j][0]:
                    B = FRAME.add(B, FRAME.mul(v, v, meter))
            for i in range(dimension):
                for j, k in combinations(chosen, 2):
                    vj, sj = basis[j]
                    vk, sk = basis[k]
                    polynomial = FRAME.add(FRAME.mul(sj, vk[i], meter), scale(FRAME.mul(sk, vj[i], meter), -1))
                    if polynomial:
                        witnesses.append(dict(coordinate=i, left=j, right=k, polynomial=FRAME.encode(polynomial)))
        slack = FRAME.add(FRAME.mul(B, S, meter), scale(P, -1))
        restored_slack = {}
        for witness in witnesses:
            poly = decode(witness['polynomial'])
            restored_slack = FRAME.add(restored_slack, FRAME.mul(poly, poly, meter))
        if slack != restored_slack:
            raise ArithmeticError('exact quotient or complete Lagrange square certificate')
        G, J = {}, {}
        for i, w in enumerate(W):
            G = FRAME.add(G, w)
            J = FRAME.add(J, scale(FRAME.mul(w, {(i,): Q(1)}, meter), -1))
        if G != S or J:
            raise ArithmeticError('exact recovery retains the full original common mode')
        common_mode = dict(unnormalized_G_coefficient=FRAME.encode(G), unnormalized_J_coefficient=FRAME.encode(J),
            unnormalized_paid_coefficients=[FRAME.encode(scale(w, -1)) for w in W], normalized_G_coefficient='1',
            classification='equivalent_to_full_core_modulo_paid_vector_and_recovery_cost',
            remaining_signed_bound='open', uniform_signed_control_added=False)
        points = [list(map(Q, range(1, dimension+1)))]+[
            [Q(i == j) for i in range(dimension)] for j in range(dimension)]
        for d in points:
            s, p, b = [value(poly, d, meter) for poly in (S, P, B)]
            if s > 0 and b > 0:
                break
        else:
            raise ValueError('no countermodel point for this nonzero homogeneous frame')
        K, rho = p/s**2, s/(2*b)
        weights = [value(w, d, meter)/s for w in W]
        if sum(weights) != 1 or sum(w*t for w, t in zip(weights, d)) or K > 1/rho:
            raise ArithmeticError('bounded recovery and unbounded free common mode')
        countermodel = dict(drifts=list(map(str, d)), normalizer=str(s), numerator=str(p), bound_numerator=str(b),
            recovery_cost=str(K), rho=str(rho), margin=str(s-rho*b), weights=list(map(str, weights)),
            common_mode_slope=str(sum(weights)), residual_energy='T^2 for arbitrary real T on a unit abstract Hilbert vector H',
            source_AST_satisfied=False, actual_source_bound_disproved=False, recovery_condition_satisfied=True)
        certificates.append(dict(id=candidate['id'], recovery_numerator=FRAME.encode(P),
            division=dict(quotient=FRAME.encode(quotient), remainder=FRAME.encode(remainder)), branch=branch,
            bound_numerator=FRAME.encode(B), slack=FRAME.encode(slack), sos=witnesses,
            common_mode=common_mode, arithmetic_condition=condition(S, B), countermodel=countermodel,
            universal_recovery_reduction_proved=True, uniform_actual_recovery_proved=False,
            uniform_actual_residual_proved=False))
        meter.live(2000*(len(certificates)+len(witnesses)))
    return dict(schema='core-frame-bound-synthesis-v1', dimension=dimension, certificates=certificates,
        statistics=dict(candidates=len(certificates), exact_quotients=sum(c['branch'] == 'exact_quotient' for c in certificates),
            cauchy_quotients=sum(c['branch'] == 'cauchy_quotient' for c in certificates),
            sos_squares=sum(len(c['sos']) for c in certificates)),
        whole_signed_bound_proved=False, RH_proved=False)


def feedback(parent, certificate, source_references):
    """Compile a new sufficient arithmetic lemma without dropping the old goal."""
    if parent['candidate_id'] != certificate['id'] or parent['whole_signed_bound_proved']:
        raise ValueError('same open inherited construction')
    return dict(id='frame_bound_'+str(certificate['id']), candidate_id=certificate['id'],
        parent_construction=parent, source_representations=source_references,
        generated_arithmetic_condition=certificate['arithmetic_condition'],
        recovery_certificate_branch=certificate['branch'],
        exact_certificate_file='core-frame-bound-results/pilot-001/certificates.json',
        conditional_recovery='pointwise K<=B/S; the cofinal arithmetic condition would prove K<=c^(-1)*(1+log2X)^q',
        automatic_equivalence_audit=certificate['common_mode'],
        proof_dependency_graph=[
            dict(id='exact_frame_identity', status='proved', depends_on=[]),
            dict(id='universal_quotient_reduction', status='proved', depends_on=['exact_frame_identity']),
            dict(id='arithmetic_quadratic_lower_bound', status='open', depends_on=[]),
            dict(id='uniform_recovery_cost', status='conditional', depends_on=['universal_quotient_reduction', 'arithmetic_quadratic_lower_bound']),
            dict(id='full_signed_residual_control', status='open', depends_on=[]),
            dict(id='core_control', status='conditional', depends_on=['uniform_recovery_cost', 'full_signed_residual_control', 'inherited_recovery_and_finite_head']),
            dict(id='inherited_recovery_and_finite_head', status='open', depends_on=[])],
        search_feedback=dict(
            recovery_target='prove the emitted quadratic form in COMPLETE signed Mobius moments is nonnegative, with positive denominator, uniformly at the stated cofinal scales',
            residual_target='find an independent source-specific estimate for the joined residual or its scale recurrence',
            equivalent_rewrite_credit=0,
            abstract_frame_facts_sufficient_for_residual=False,
            actual_source_bound_disproved=False,
            unknown_arithmetic_lemmas_remain_admissible=True),
        original_target_and_all_crosses_retained=True, all_scale_signed_control_proved=False,
        whole_signed_bound_proved=False, RH_proved=False)


def substitute(poly, images, meter):
    """Exact composition; repeated source moments stay the same variable."""
    result = {}
    for monomial, coefficient in poly.items():
        term = {(): coefficient}
        for index in monomial:
            term = FRAME.mul(term, images[index], meter)
        result = FRAME.add(result, term)
    return result


def source_conditions(representations, certificates, meter):
    variables, lookup = [], {}
    for kind, key, power in [('a', 'alpha', '2/3'), ('b', 'gamma', '4/3')]:
        for exponent in sorted({g[key] for g in representations}, key=Q):
            lookup[(kind, exponent)] = len(variables)
            variables.append(dict(id=len(variables), kind='complete_mobius_moment', family=kind,
                moment_power=power, cutoff_exponent=exponent,
                definition='sum_(1<=n<=floor(N^cutoff_exponent)) mu(n)*n^(-moment_power)',
                unit_and_prime_powers_retained=True))
    ru = len(variables)
    variables.append(dict(id=ru, kind='source_scalar', name='R_u',
        definition='(9/2)*(zeta(4/3)/zeta(2/3)^2-1/zeta(2/3))'))
    drifts = []
    for g in representations:
        if g['drift']['theta'] != '2/3':
            raise ValueError('actual complete source moment power binding')
        terms = {}
        for term in g['drift']['polynomial']:
            pa, pb, pc, pr = term['powers']
            if pc:
                raise ValueError('complete c_U moment is not silently omitted')
            key = tuple(sorted([lookup[('a', g['alpha'])]]*pa+[lookup[('b', g['gamma'])]]*pb+[ru]*pr))
            terms = FRAME.add(terms, {key: Q(term['coefficient'])})
        drifts.append(terms)
    results = []
    for cert in certificates:
        S = substitute(decode(cert['arithmetic_condition']['left']), drifts, meter)
        B = substitute(decode(cert['bound_numerator']), drifts, meter)
        results.append(dict(candidate_id=cert['id'], variables=variables,
            geometry_order=[g['geometry_id'] for g in representations],
            complete_drift_polynomials=list(map(FRAME.encode, drifts)),
            denominator=FRAME.encode(S), recovery_bound_numerator=FRAME.encode(B),
            rho=cert['arithmetic_condition']['rho'], parameters=cert['arithmetic_condition']['parameters'],
            quantifier=cert['arithmetic_condition']['quantifier'], required='S>0 and S>=rho*B',
            common_horizon='N=4X-1', all_shared_moments_identified=True,
            algebraic_substitution_proved=True, arithmetic_inequality_proved=False, status='open'))
    return results
