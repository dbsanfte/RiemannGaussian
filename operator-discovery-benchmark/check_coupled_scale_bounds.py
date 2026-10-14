"""Source-bound helper prices and an OPEN coupled energy recurrence.

This is independent of the candidate producer and evidence worker. Admission
proves the helper/recovery bounds and a conditional implication; it never
proves the displayed arithmetic recurrence from finite evidence.
"""
import copy
from fractions import Fraction as F
from math import comb

import check_prime_cofactor_discovery as BASE


_CONTEXTS = {}


class _Context:
    """An in-memory admission handle; caller data never licenses premises."""
    __slots__ = ('__weakref__',)


def _actual_source():
    return dict(lattice=6, channels=[
        dict(atoms=[dict(kind='power', shift=2), dict(kind='mu', shift=0),
                    dict(kind='mu', shift=0)], weight=['9/2', '0']),
        dict(atoms=[dict(kind='power', shift=2), dict(kind='mu', shift=0),
                    dict(kind='mu', shift=4)], weight=['-9/2', '0']),
        dict(atoms=[dict(kind='power', shift=2), dict(kind='mu', shift=4)], weight=['0', '-1']),
        dict(atoms=[dict(kind='mu', shift=0)], weight=['-9/2', '0'])])


def prepare(basecert, meter=None):
    """Replay one exact source certificate and retain private admitted data."""
    meter = BASE._meter(meter)
    BASE._require(type(basecert) is dict and BASE._same(basecert.get('source'), _actual_source()),
                  'the complete original four-channel source, units and scalars are required')
    admitted = BASE.verify(basecert['source'], basecert, meter)
    _local_coefficient_rules(meter)
    helpers = []
    for frontier, unit in zip(admitted['frontier_bounds'], admitted['unit']):
        BASE._require(frontier['r'] is not None, 'this provider requires a nonzero prime profile')
        r = BASE._q(frontier['r'], meter)
        BASE._require(0 <= r < 1, 'this helper provider requires a prime exponent below one')
        J = BASE._q(frontier['unit_ceiling'], meter)
        D = BASE._q(frontier['coefficient_ceiling'], meter)
        a = 1-r
        K = BASE._checked(J+D/(1-r), meter)
        constant = BASE._checked(K*K*F(1 << (2*((a.numerator+a.denominator-1)//a.denominator))), meter)
        helpers.append(dict(a=a, constant=constant, K=K, J=J, D=D, r=r,
                            unit=tuple(BASE._q(unit[k], meter) for k in ('constant', 'R'))))
    context = _Context()
    _CONTEXTS[context] = dict(source=copy.deepcopy(basecert['source']),
        states=copy.deepcopy(basecert['states']), certificate=copy.deepcopy(basecert),
        helpers=helpers, admitted=copy.deepcopy(admitted), meter=meter)
    return context


def _program(data, helpers, meter):
    BASE._require(type(data) is dict and set(data) == {'id', 'program', 'recurrence_C'},
                  'candidate consists only of id, exact helper program and recurrence_C')
    BASE._require(type(data['id']) is str and 1 <= len(data['id']) <= 256,
                  'bounded nonempty candidate id')
    C = BASE._q(data['recurrence_C'], meter)
    BASE._require(C >= 0, 'nonnegative uniform recurrence forcing constant')
    raw = data['program']
    BASE._require(type(raw) is list and len(raw) <= 64, 'bounded complete helper program')
    result = []
    for term in raw:
        BASE._require(type(term) is dict and set(term) == {'state', 'divisor', 'exponent', 'coefficient'},
                      'exact helper term schema')
        i, d = term['state'], term['divisor']
        BASE._require(type(i) is int and 0 <= i < len(helpers), 'source-bound state index')
        BASE._require(type(d) is int and d >= 1 and d.bit_length() <= 4096,
                      'positive bounded integer divisor')
        gamma, c = BASE._q(term['exponent'], meter), BASE._q(term['coefficient'], meter)
        BASE._require(gamma >= 0 and c != 0, 'nonnegative exact exponent and nonzero signed coefficient')
        required = max(F(0), (2*helpers[i]['a']-1)/2)
        BASE._require(gamma >= required, 'helper exponent must pay its complete block energy')
        result.append(dict(state=i, divisor=d, gamma=gamma, c=c))
    return result, C


def _defect(program, C, meter):
    """Expand the two child squares and parent square before any bound."""
    terms, definitions = [], []
    branches = [(2, '2*n', F(1)), (2, '2*n+1', F(1)), (1, 'n', F(-4))]
    for scale, argument, branch_weight in branches:
        name = 'child_even' if argument == '2*n' else 'child_odd' if argument == '2*n+1' else 'parent'
        variables = [dict(id=name+':F', kind='complete_source_prefix', argument=argument,
                          coefficient='1', X_power='0', scale_power='0')]
        for j, term in enumerate(program):
            variables.append(dict(id=name+':H'+str(j), kind='explicit_prime_profile',
                state=term['state'], argument='floor(('+argument+')/'+str(term['divisor'])+')',
                cutoff='ceil(sqrt('+str(2*scale)+'*X))', coefficient=str(term['c']),
                X_power=str(-term['gamma']), scale_power=str(-term['gamma'])))
        definitions.extend(variables)
        for i, left in enumerate(variables):
            for j in range(i, len(variables)):
                right = variables[j]
                coefficient = BASE._checked(branch_weight * (1 if i == j else 2) *
                    F(left['coefficient'])*F(right['coefficient']), meter)
                power = BASE._checked(F(left['X_power'])+F(right['X_power']), meter)
                terms.append(dict(branch=name, factors=[left['id'], right['id']],
                    coefficient=str(coefficient), X_power=str(power), scale_base=scale,
                    scale_power=str(power)))
    return dict(identity='4*X^2*(E_G(2X)-E_G(X)-C*D(X))',
        n_domain='every integer n=X..2X-1', variables=definitions, quadratic_terms=terms,
        coefficient_square_forcing=dict(coefficient=str(-4*C), X_power='1',
            expression='sum_(k=1..4X-1) f(k)^2'),
        all_helper_crosses=True, odd_child_endpoint_retained=True,
        all_moving_scale_and_cutoff_factors_retained=True,
        prefix_below_one='0', helper_unit_retained=True,
        variable_values_are_unweighted_prefixes=True,
        coefficient_policy='quadratic coefficients include program coefficients and cross factors once; X_power and scale_power carry scale weights once')


def _countermodel(program, helpers, C, meter):
    """An exact failure of the norm-only rule, not of the source recurrence."""
    # Free parameter R=2 lies in the coefficient-envelope interval. The exact
    # zeta specialization and all source Euler identities are NOT premises here.
    units = [h['unit'][0]+2*h['unit'][1] for h in helpers]
    M = BASE._checked(sum((abs(t['c'])*abs(units[t['state']]) for t in program), F(0)), meter)
    threshold = max(F(32), 2*M*M, 12*M+90*C+4)
    needed = (threshold.numerator+threshold.denominator-1)//threshold.denominator
    exponent = (needed-1).bit_length()
    BASE._require(exponent <= 32768, 'generic countermodel exceeds verifier rational resource limit')
    X = 1 << exponent
    # E_F(X)=7X/3-24+767/(12X), for f1=-13/2,f(n>=2)=1.
    # Each G-F has magnitude<=M. For X>=32 its energy perturbation
    # is <=3M+M²/X; both scales are covered by one bound.
    lower = BASE._checked(F(7,3)*X-F(767,24*X)-6*M-F(3,2)*M*M/X, meter)
    forcing_ceiling = BASE._checked(45*C, meter)  # D(X)=4+161/(4X)<45.
    margin = BASE._checked(lower-forcing_ceiling, meter)
    BASE._require(margin > 0, 'strict exact generic norm-rule counterexample')
    return dict(status='GENERIC_ENVELOPE_RULE_REJECTED',
        scope='generic coefficient and helper norm envelopes only; not the actual arithmetic source',
        exact_countermodel=dict(R='2', source_unit='-13/2',
            source_coefficients='f(1)=-13/2; f(n)=1 for every integer n>=2',
            helper_units=[str(u) for u in units], helper_prime_coefficients='0',
            helper_prefix='unit_i for t>=1; 0 for t<1',
            every_helper_partial_prefix_and_unit_retained=True,
            helper_total_absolute_ceiling=str(M), X=str(X), dyadic_exponent=exponent,
            full_prefix_energy='7*X/3-24+767/(12*X)',
            coefficient_energy='4+161/(4*X)',
            recurrence_defect_lower=str(lower), forcing_upper=str(forcing_ceiling),
            positive_margin=str(margin),
            source_coefficient_envelope_satisfied=True, helper_envelopes_satisfied=True,
            actual_zeta_R_binding_satisfied=False, all_prime_source_laws_satisfied=False,
            actual_source_recurrence_refuted=False),
        implication='pointwise coefficient/helper envelopes alone cannot prove the proposed recurrence',
        broader_arithmetic_proof_grammar_refuted=False)


def _local_coefficient_rules(meter):
    """Exact polynomial positivity for the local coefficient envelopes."""
    polynomials = [('2-a', [F(2),F(-1)]), ('a', [F(0),F(1)]),
                   ('1-a+a^2', [F(1),F(-1),F(1)]),
                   ('a-a^2', [F(0),F(1),F(-1)]),
                   ('1-a', [F(1),F(-1)])]
    witnesses = []
    for name, coefficients in polynomials:
        degree = len(coefficients)-1
        bernstein = [BASE._checked(sum((coefficients[j]*F(comb(i,j),comb(degree,j))
                     for j in range(i+1)), F(0)),meter) for i in range(degree+1)]
        BASE._require(all(value>=0 for value in bernstein), 'local polynomial envelope on[0,1]')
        witnesses.append(dict(polynomial=name, bernstein_coefficients=[str(x) for x in bernstein]))
    BASE._require(F(9,2)+F(9,2)+F(5)+F(9,2)==F(37,2), 'complete source coefficient triangle')
    BASE._require(F(37,2)**2*4*27==36963, 'full horizon coefficient energy constant')
    return witnesses


def _divisor_provider(meter):
    return dict(source_coefficient_constant='37/2', source_coefficient_bound='abs(f(n))<=(37/2)*d_2(n)',
        local_proofs=[
            dict(mode='nu0', first='abs(a-2)<=2', tail='a^(e-2)*(1-a)^2<=1 for e>=2', bound='d_2(n)'),
            dict(mode='nu1', first='1-a+a^2<=1', tail='a^(e-1)*(1-a)^2<=1 for e>=2', bound='1'),
            dict(mode='nu2', first='a-a^2<=1', tail='a^e*(1-a)<=1 for e>=2', bound='1'),
            dict(mode='mu', bound='1')],
        domain='all primes, a=p^(-1/3) in(0,1); all valuations including zero',
        polynomial_nonnegative_certificates=_local_coefficient_rules(meter),
        divisor_square_identity='d_4(p^e)-d_2(p^e)^2=(e+1)*e*(e-1)/6>=0 for every integer e>=0',
        divisor_sum='sum_(n<=N)d_4(n)<=N*(1+log(N))^3',
        divisor_sum_proof='count ordered divisor quadruples; three harmonic sums after floor(N/(abc))<=N/(abc)',
        D_definition='X^-1*sum_(n<=4X-1) f(n)^2',
        bound=dict(constant='36963', log_power=3, domain='every integer X>=1'),
        constant_derivation='(37/2)^2*4*27=36963; 1+log(4X)<=3*(1+log(X))')


def verify_candidate(context, candidate):
    BASE._require(type(context) is _Context and context in _CONTEXTS,
                  'prepare must admit the exact base source before candidate verification')
    data = _CONTEXTS[context]
    meter, helpers = data['meter'], data['helpers']
    program, C = _program(candidate, helpers, meter)
    price_rows = []
    for term in program:
        h = helpers[term['state']]
        price_rows.append(dict(state=term['state'], divisor=term['divisor'],
            exponent=str(term['gamma']), coefficient=str(term['c']),
            prime_exponent=str(h['r']), prefix_constant=str(h['K']), prefix_power=str(h['a']),
            unscaled_energy_constant=str(h['constant']),
            scaled_energy_power=str(2*h['a']-1-2*term['gamma']),
            required_exponent=str(max(F(0), (2*h['a']-1)/2)),
            complete_real_partial_prefix_scope='1<=t<=2X, at one shared y=ceil(sqrt(2X))',
            coefficient_twist_is_not_applied_to_the_complete_F=True))
    KH = BASE._checked(len(program)*sum((t['c']**2*helpers[t['state']]['constant']
                                        for t in program), F(0)), meter)
    head = [F(-9,2), F(-1)]
    for term in program:
        if term['divisor'] == 1:
            head = [BASE._checked(x+term['c']*u, meter)
                    for x,u in zip(head,helpers[term['state']]['unit'])]
    Chead = BASE._checked(max((head[0]+head[1])**2, (head[0]+5*head[1])**2), meter)
    conditional_dyadic = BASE._checked(2*(Chead+KH)+147852*C, meter)
    log_power, covering = (0, 5) if C == 0 else (4, 65)
    integer_constant = BASE._checked(covering*conditional_dyadic, meter)
    recurrence_id = candidate['id']+':actual_arithmetic_recurrence'
    dependency_graph = [
        dict(id='base_source', status='PROVED', requires=[]),
        dict(id='helper_prices', status='PROVED', requires=['base_source']),
        dict(id='divisor_forcing', status='PROVED', requires=['base_source']),
        dict(id='unit_head', status='PROVED', requires=['base_source']),
        dict(id=recurrence_id, status='OPEN', requires=['base_source']),
        dict(id='conditional_recovery', status='CONDITIONAL', requires=[
            'helper_prices','divisor_forcing','unit_head',recurrence_id]),
        dict(id='full_signed_core', status='OPEN', requires=['conditional_recovery'])]
    _verify_dependencies(dependency_graph)
    return dict(verified=True, candidate_id=candidate['id'],
        meaning_of_verified='paid helpers/head and a conditional implication; not recurrence admission',
        source_binding=copy.deepcopy(data['source']), state_programs=copy.deepcopy(data['states']),
        R_enclosure=data['admitted']['R_enclosure'],
        paid_helper=dict(constant=str(KH), terms=price_rows,
            rule='k*sum_i c_i^2*C_i', recovery='E_F(X)<=2*E_G(X)+2*K_H for every integer X>=1'),
        paid_head=dict(constant=str(Chead), affine_value=[str(x) for x in head],
                       block='X=1,n=1; only divisor1 helper units contribute'),
        forcing_provider=_divisor_provider(meter),
        conditional_G_dyadic=dict(head_constant=str(Chead), forcing_constant=str(73926*C),
            log_power=log_power, requires_open_recurrence=True),
        conditional_F_dyadic=dict(constant=str(conditional_dyadic), log_power=log_power,
                                  requires_open_recurrence=True),
        conditional_energy_bound=dict(constant=str(integer_constant), log_power=log_power,
            scope='all integer X>=1', requires_open_recurrence=True,
            dyadic_covering_factor=str(covering), covering_applies_to='complete original F only'),
        epsilon_conversion=dict(epsilon_domain='every real epsilon>0',
            factor='1' if C == 0 else '8*(1+24*epsilon^(-4))',
            estimate='1<=X^epsilon' if C == 0 else '(1+log(X))^4<=8*(1+24*epsilon^(-4))*X^epsilon'),
        open_recurrence=dict(id=recurrence_id,
            statement='E_G(2X)<=E_G(X)+C*D(X)',
            domain='every dyadic integer X>=1, with C independent of X and all cutoffs',
            source_binding=copy.deepcopy(data['source']), program=copy.deepcopy(candidate['program']),
            C=str(C), status='OPEN', defect_expansion=_defect(program,C,meter)),
        proof_attempt=_countermodel(program,helpers,C,meter), dependency_graph=dependency_graph,
        inherited_source_and_transport_obligations_discharged=False,
        recurrence_proved=False, whole_signed_bound_proved=False, RH_proved=False)


def _verify_dependencies(graph):
    seen = {}
    for node in graph:
        BASE._require(type(node) is dict and set(node)=={'id','status','requires'} and
                      node['status'] in ('PROVED','OPEN','CONDITIONAL') and
                      type(node['requires']) is list, 'typed proof dependency node')
        BASE._require(node['id'] not in seen, 'distinct dependency ids')
        BASE._require(all(key in seen for key in node['requires']), 'topological proof dependencies')
        if node['status'] == 'PROVED':
            BASE._require(all(seen[key] == 'PROVED' for key in node['requires']),
                          'a proved node cannot depend on an open or conditional premise')
        seen[node['id']] = node['status']


def verify_result(context, candidate, result):
    """Optional publication admission: reject mutated conditional output."""
    expected = verify_candidate(context,candidate)
    BASE._require(BASE._same(result,expected), 'all source, defect, cost and open dependency fields')
    return dict(verified=True, recurrence_proved=False, whole_signed_bound_proved=False, RH_proved=False)
