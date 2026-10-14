"""Small independent certificate replay; imports no generator or selector."""
from fractions import Fraction as Q
from math import ceil, factorial


def shifted_coefficients(coefficients):
    # Polynomial Horner composition p(1-z), independently of the producer's
    # binomial transform and root-order implementation.
    result = []
    for c in reversed(coefficients):
        nxt = [Q(0)] * (len(result) + 1)
        for j, value in enumerate(result):
            nxt[j] += value
            nxt[j+1] -= value
        nxt[0] += Q(c)
        result = nxt
    return result


def check_program(program, meter):
    channels = program['channels']
    a = list(map(Q, program['recovery_coefficients']))
    if not channels or len(channels) != len(a) or not all(a):
        raise ValueError('complete nonredundant recovery channels')
    identity = [Q(0)]*max(len(c['polynomial']) for c in channels)
    constants, powers, etas = [], [], []
    for channel, coefficient in zip(channels, a):
        p = list(map(Q, channel['polynomial']))
        eta = Q(channel['eta'])
        if not p or not p[-1] or eta < 0:
            raise ValueError('channel domain')
        for j, c in enumerate(p):
            identity[j] += coefficient*c
        b = shifted_coefficients(p)
        first = next(i for i, c in enumerate(b) if c)
        if channel['shifted_coefficients'] != list(map(str, b)) or first != channel['vanishing_order']:
            raise ArithmeticError('unverified leading-term cancellation')
        terms, total = [], Q(0)
        for q, bq in enumerate(b):
            if not bq:
                continue
            cq = sum(Q(factorial(q), factorial(j)) for j in range(q+1))
            previous = sum(Q(factorial(q-1), factorial(j)) for j in range(q)) if q else Q(0)
            h = q*previous + (q+eta)*cq
            # 2^ceil(2(q+eta)) replaces the irrational power upwards.
            D = (32 + 8*h*h)*2**ceil(2*(q+eta))
            total += abs(bq)*D
            terms.append(dict(q=q, coefficient=str(bq), constant=str(D)))
        total *= sum(map(abs, b))
        power = 3-2*(first+eta)
        if channel['terms'] != terms or Q(channel['derivative_constant']) != total or Q(channel['derivative_log_power']) != power:
            raise ArithmeticError('derivative certificate or fractional exponent')
        if not channel['full_unit_retained']:
            raise ValueError('complete prefix required')
        constants.append(total)
        powers.append(power)
        etas.append(eta)
        meter.charge(600*len(p))
    if identity != [Q(1)] + [Q(0)]*(len(identity)-1):
        raise ArithmeticError('no exact full-source recovery')
    ell = 2*max(etas)
    c_rec = sum(v*v for v in a)*2**ceil(ell)
    expected = dict(recovery_constant=c_rec, recovery_log_power=ell,
                    detail_constant_times_K_squared=sum(constants)/8,
                    detail_log_power=max(powers), recovered_detail_log_power=max(powers)+ell)
    for key, value in expected.items():
        if Q(program[key]) != value:
            raise ArithmeticError('incorrect combined cost: '+key)
    for key in ('uniform_coarse_bound_proved', 'whole_signed_bound_proved', 'RH_proved'):
        if program[key]:
            raise ValueError('an open signed arithmetic leaf cannot be declared proved')
    # Identity at t=1 requires a nonvanishing channel. With these rules,
    # total derivative log payment at the square-root mesh is at least3.
    if max(powers)+ell < 3:
        raise ArithmeticError('hidden recovery cost')
    return dict(verified=True, conditional_on_source_majorant=True,
                uniform_coarse_bound_proved=False, original_target_proved=False)


def check_branch(program, branch, meter):
    r, p, rho = (Q(branch[key]) for key in ('mesh_power', 'target_log_power', 'rho'))
    if not (0 < r <= 1 and p >= 0 and 0 < rho <= 1):
        raise ValueError('branch domain')
    e = 2*r-1
    m, ell = map(Q, (program['recovered_detail_log_power'], program['recovery_log_power']))
    k = p-ell-(1 if rho == 1 else 0)
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
            t = max(0, ceil(m))
            absorption = Q(1) if t == 0 else Q(2)*factorial(t)*(Q(2)/(-e))**t
    if (branch['status'], Q(branch['detail_X_power']), Q(branch['required_coarse_forcing_log_power'])) != (status, e, k):
        raise ArithmeticError('backward target propagation')
    if branch['detail_absorption_constant'] != (str(absorption) if absorption is not None else None):
        raise ArithmeticError('missing uniform power/log payment')
    if branch['full_bound_proved'] or branch['open_leaf_count'] != 1:
        raise ValueError('coarse obligation remains open')
    meter.charge(80)
    return True


def check_dependency_graph(obligation):
    nodes = {node['id']: node for node in obligation['dependency_graph']}
    if len(nodes) != len(obligation['dependency_graph']):
        raise ValueError('duplicate dependency')
    done, visiting = set(), set()
    def visit(name):
        if name in visiting:
            raise ValueError('circular proof')
        if name in done:
            return
        visiting.add(name)
        node = nodes[name]
        for parent in node['depends_on']:
            visit(parent)
        if node['status'] == 'proved' and any(nodes[p]['status'] != 'proved' for p in node['depends_on']):
            raise ValueError('open dependency promoted to a theorem')
        visiting.remove(name)
        done.add(name)
    for name in nodes:
        visit(name)
    if nodes['signed_coarse_increment']['status'] != 'open' or obligation['required']['proved']:
        raise ValueError('this proof library does not close the signed coarse estimate')
    if obligation['whole_signed_bound_proved'] or obligation['RH_proved']:
        raise ValueError('unsupported full conclusion')
    return True
