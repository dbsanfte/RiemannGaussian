"""Independent exact proof-certificate replay and joined-source evaluator071.

No producer, optimizer, old checker, numerical array package or frontier
formula is imported. Arithmetic mu enters only the final finite evaluator.
"""
from fractions import Fraction as Q
from math import isqrt, isfinite
import time

MAX_BYTES = 2 * 1024**3
MAX_POWER_BITS = 100_000
FLAGS = ('conditional_prefix_bounds_paid', 'uniform_head_bound_proved', 'RH_proved')


class Meter:
    def __init__(self, limit=300_000_000_000, seconds=7200):
        self.limit, self.seconds = limit, seconds
        self.operations = 0
        self.started = time.monotonic()

    def charge(self, count=1):
        require(type(count) is int and count >= 0, 'invalid work charge')
        self.operations += count
        require(self.operations <= self.limit, 'checker work limit exceeded')
        require(time.monotonic() - self.started <= self.seconds, 'checker time limit exceeded')

    add = charge


def require(condition, message):
    if not condition:
        raise ValueError(message)


def keys(obj, names, label):
    require(type(obj) is dict and set(obj) == set(names.split()), label + ' keys')


def integer(value, lo=None, hi=None):
    require(type(value) is int and value.bit_length() <= 4096, 'bounded integer required')
    require(lo is None or value >= lo, 'integer lower gate')
    require(hi is None or value <= hi, 'integer upper gate')
    return value


def rational(value):
    require(type(value) is str and 0 < len(value) <= 2500, 'bounded rational string')
    parts = value.split('/')
    require(len(parts) in (1, 2), 'rational syntax')
    require(all(p and p.isascii() and p.removeprefix('-').isdigit() for p in parts), 'rational syntax')
    require(all(len(p) <= 1235 for p in parts), 'rational decimal capacity')
    nums = [int(p) for p in parts]
    require(all(abs(n).bit_length() <= 4096 for n in nums), 'rational bit capacity')
    require(len(nums) == 1 or nums[1] > 0, 'positive denominator')
    result = Q(*nums)
    require(str(result) == value, 'canonical rational required')
    return result


def qtext(value):
    value = Q(value)
    def decimal(n):
        if abs(n).bit_length() < 12_000:
            return str(n)
        sign = '-' if n < 0 else ''
        n, chunks = abs(n), []
        while n:
            n, part = divmod(n, 1_000_000_000)
            chunks.append(part)
        return sign + str(chunks[-1]) + ''.join(f'{p:09d}' for p in reversed(chunks[:-1]))
    return decimal(value.numerator) if value.denominator == 1 else decimal(value.numerator)+'/'+decimal(value.denominator)


def bounded(value):
    require(max(abs(value.numerator).bit_length(), value.denominator.bit_length()) <= MAX_POWER_BITS,
            'rational intermediate bit gate')
    return value


def scan(value, meter):
    """Prospective conservative JSON-object bound, before any replay expansion."""
    state = [0, 0]
    def visit(x, depth):
        meter.charge()
        state[0] += 1
        require(depth <= 32 and state[0] <= 8_000_000, 'input complexity gate')
        state[1] += 128
        if type(x) is dict:
            state[1] += len(x) * 64
            for name, item in x.items():
                require(type(name) is str, 'JSON string key required')
                state[1] += len(name) * 4
                visit(item, depth + 1)
        elif type(x) is list:
            state[1] += len(x) * 16
            for item in x:
                visit(item, depth + 1)
        elif type(x) is str:
            state[1] += 4 * len(x)
        elif type(x) is int:
            integer(x)
        elif type(x) is float:
            require(isfinite(x), 'finite observational metadata required')
        else:
            require(x is None or type(x) is bool, 'JSON value required')
        require(state[1] <= MAX_BYTES, 'checker prospective 2GiB memory gate')
    visit(value, 0)
    return state[1]


def flags(cert):
    for name in FLAGS:
        require(cert[name] is False, 'unsupported uniform proof claim')


def system(variables, rows, objective):
    return dict(variables=variables, rows=[dict(name=n, a=[str(Q(x)) for x in a], b=str(Q(b)))
                                         for n, a, b in rows], objective=[str(Q(x)) for x in objective])


def primary_system(sigma, rho, theta):
    rows = [('theta_lower', [1, 0, 0, 0, 0], 0),
            ('theta_upper', [-1, 0, 0, 0, 0], -1),
            ('u_domain', [-1, 1, 0, 0, 0], 0),
            ('v_domain', [1, 0, 1, 0, 0], 1),
            ('u_rank', [0, -1, 0, 0, 0], -rho),
            ('v_rank', [0, 0, -1, 0, 0], -rho),
            ('u_exposure', [-1, 1, 0, 1, 0], 0),
            ('u_moment', [1-sigma, 0, 0, 1, 0], 0),
            ('v_exposure', [1, 0, 1, 0, 1], 1),
            ('v_moment', [sigma-1, 0, 0, 0, 1], sigma-1),
            ('u_nonpositive', [0, 0, 0, -1, 0], 0),
            ('v_nonpositive', [0, 0, 0, 0, -1], 0)]
    if theta is not None:
        rows += [('fixed_theta_lower', [1, 0, 0, 0, 0], theta),
                 ('fixed_theta_upper', [-1, 0, 0, 0, 0], -theta)]
    return system(['theta', 'gamma_u', 'gamma_v', 'kappa_u', 'kappa_v'], rows, [0, 0, 0, 1, 1])


def secondary_system(primary, optimum):
    rows = [(r['name'], [rational(x) for x in r['a']] + [0], rational(r['b'])) for r in primary['rows']]
    rho = -rational(primary['rows'][4]['b'])
    rows += [('optimum_lower', [0, 0, 0, 1, 1, 0], optimum),
             ('optimum_upper', [0, 0, 0, -1, -1, 0], -optimum),
             ('exposure_u', [0, -1, 0, 0, 0, 1], 0),
             ('exposure_v', [0, 0, -1, 0, 0, 1], 0),
             ('exposure_lower', [0, 0, 0, 0, 0, 1], 0),
             ('exposure_upper', [0, 0, 0, 0, 0, -1], -rho)]
    return system(primary['variables'] + ['exposure'], rows, [0, 0, 0, 0, 0, 1])


def short_system(sigma):
    return system(['split', 'delta'], [('split_lower', [1, 0], 0),
                  ('split_upper', [-1, 0], -1), ('short_prefix', [sigma-1, 1], sigma),
                  ('short_tail', [1, 1], 1), ('delta_upper', [0, -1], -1)], [0, 1])


def dot(a, b, meter):
    result = Q(0)
    for x, y in zip(a, b):
        meter.charge(1 + abs(x.numerator).bit_length() + x.denominator.bit_length()
                     + abs(y.numerator).bit_length() + y.denominator.bit_length())
        result = bounded(result + bounded(x*y))
    return result


def check_lp(record, expected, meter):
    keys(record, 'system result', 'LP record')
    require(record['system'] == expected, 'literal affine system mismatch')
    # Equality above is safe: expected numerical entries are canonical strings.
    r = record['result']
    require(type(r) is dict and r.get('status') in ('optimal', 'infeasible', 'unresolved'), 'LP status')
    status = r['status']
    keys(r, {'optimal': 'status primal dual objective solver',
             'infeasible': 'status dual solver', 'unresolved': 'status reason solver'}[status], 'LP result')
    require(type(r['solver']) is dict, 'observational solver metadata')
    if status == 'unresolved':
        require(type(r['reason']) is str and bool(r['reason']), 'unresolved reason')
        return dict(status=status)
    A = [[rational(v) for v in row['a']] for row in expected['rows']]
    b = [rational(row['b']) for row in expected['rows']]
    c = [rational(v) for v in expected['objective']]
    require(type(r['dual']) is list and len(r['dual']) == len(A), 'complete dual vector')
    y = [rational(v) for v in r['dual']]
    require(all(v >= 0 for v in y), 'nonnegative dual required')
    target = c if status == 'optimal' else [Q(0)] * len(c)
    for col, value in enumerate(target):
        require(dot([row[col] for row in A], y, meter) == value, 'exact dual stationarity')
    dual_value = dot(b, y, meter)
    if status == 'infeasible':
        require(dual_value == 1, 'normalized Farkas contradiction')
        return dict(status=status)
    require(type(r['primal']) is list and len(r['primal']) == len(c), 'complete primal vector')
    x = [rational(v) for v in r['primal']]
    for row, rhs in zip(A, b):
        require(dot(row, x, meter) >= rhs, 'exact primal feasibility')
    value = rational(r['objective'])
    require(dot(c, x, meter) == value == dual_value, 'exact primal dual objective equality')
    return dict(status=status, primal=x, objective=value)


def derive(sigma, secondary, short):
    theta, gu, gv, ku, kv, exposure = secondary['primal']
    alpha = bounded(1 + ku + kv)
    require(0 < alpha <= 1 and 0 <= exposure < 1, 'derived exponent gates')
    A = bounded((2-sigma)/(1-sigma))
    split, delta = short['primal']
    base = bounded(1/(1-exposure))
    return dict(theta=str(theta), gamma_u=str(gu), gamma_v=str(gv),
                kappa_u=str(ku), kappa_v=str(kv), exposure=str(exposure),
                alpha=str(alpha), reciprocal_A=str(A),
                head_C_polynomial=[str(bounded(8/alpha)), str(bounded(16*A/alpha)), str(bounded(8*A*A/alpha))],
                short_exponent=str(delta), short_split=str(split), short_C_exponent=str(delta),
                short_per_branch_constant=str(bounded(1+4/(1-sigma))),
                sufficient_base_log2=(base.numerator + base.denominator-1)//base.denominator)


def _program(cert, meter):
    keys(cert, 'schema sigma rho fixed_theta primary secondary short derivation ' + ' '.join(FLAGS), 'program')
    require(cert['schema'] == 'mobius-moment-scale-program-v1', 'program schema')
    flags(cert)
    sigma, rho = rational(cert['sigma']), rational(cert['rho'])
    theta = None if cert['fixed_theta'] is None else rational(cert['fixed_theta'])
    require(0 < sigma < 1 and 0 < rho < 1 and (theta is None or 0 < theta < 1), 'parameter interval')
    expected = primary_system(sigma, rho, theta)
    primary = check_lp(cert['primary'], expected, meter)
    short = check_lp(cert['short'], short_system(sigma), meter)
    secondary = None
    if cert['secondary'] is not None:
        require(primary['status'] == 'optimal', 'secondary requires exact primary optimum')
        secondary = check_lp(cert['secondary'], secondary_system(expected, primary['objective']), meter)
    complete = (primary['status'] == short['status'] == 'optimal'
                and secondary is not None and secondary['status'] == 'optimal')
    expected_derivation = derive(sigma, secondary, short) if complete else None
    require(cert['derivation'] == expected_derivation, 'complete exact derivation mismatch')
    if complete:
        integer(cert['derivation']['sufficient_base_log2'], 1)
        for name, value in cert['derivation'].items():
            if name == 'head_C_polynomial':
                for coefficient in value:
                    rational(coefficient)
            elif name != 'sufficient_base_log2':
                rational(value)
    return primary['status'], expected_derivation


def verify_program(cert, meter=None):
    meter = Meter() if meter is None else meter
    scan(cert, meter)
    status, _ = _program(cert, meter)
    return dict(verified=True, status=status, **{f: False for f in FLAGS})


def power(base, exponent, meter):
    require(type(base) is int and base >= 0 and type(exponent) is int and exponent >= 0, 'integer power domain')
    require(base <= 1 or exponent <= MAX_POWER_BITS // base.bit_length(), 'explicit power bit gate')
    meter.charge(1 + max(1, base.bit_length()) * min(exponent, MAX_POWER_BITS))
    return pow(base, exponent)


def floor_power(R, exponent, meter):
    require(R >= 1 and 0 <= exponent <= 1, 'cut exponent domain')
    if R == 1 or exponent == 0:
        return 1
    a, b = exponent.numerator, exponent.denominator
    # Reject impossible intermediates before binary-search work begins.
    power(R, max(a, b), meter)
    target = power(R, a, meter)
    lo, hi = 1, R+1
    while hi-lo > 1:
        mid = (lo+hi)//2
        if power(mid, b, meter) <= target:
            lo = mid
        else:
            hi = mid
    return lo


def ceil_power(R, exponent, meter):
    floor = floor_power(R, exponent, meter)
    if R == 1 or exponent == 0:
        return floor
    return floor if power(floor, exponent.denominator, meter) == power(R, exponent.numerator, meter) else floor+1


def parameters(obj, meter):
    require(type(obj) is dict and set(obj) in ({'primes', 'p', 'q', 'alpha', 'gamma'},
                                             {'primes', 'p', 'q', 'alpha', 'gamma', 'tau'}), 'source parameter keys')
    require(0 < rational(obj['alpha']) < 1 and rational(obj['gamma']) > 0, 'source fractional parameters')
    if 'tau' in obj:
        require(0 < rational(obj['tau']) < 1, 'source tau interval')
    primes = obj['primes']
    require(type(primes) is list and 2 <= len(primes) <= 8, 'bounded prime list')
    for p in primes:
        integer(p, 2, 1_000_000)
        for d in range(2, isqrt(p)+1):
            meter.charge()
            require(p % d, 'registered actual prime required')
    require(primes == sorted(set(primes)), 'ordered distinct primes')
    p, q = integer(obj['p']), integer(obj['q'])
    require(p in primes and q in primes and p < q, 'ordered source primes')
    return p, q


def sparse(entries, maximum, meter):
    require(type(entries) is list and len(entries) <= maximum, 'bounded sparse list')
    previous = 0
    for entry in entries:
        meter.charge()
        require(type(entry) is list and len(entry) == 2, 'sparse pair')
        index, value = integer(entry[0], previous+1, maximum), integer(entry[1])
        require(value != 0, 'nonzero sparse coefficient')
        previous = index
    return entries


def ordinary_mu(D, meter):
    mu, least, primes = [0]*(D+1), [0]*(D+1), []
    mu[1] = 1
    for n in range(2, D+1):
        meter.charge()
        if not least[n]:
            least[n], mu[n] = n, -1
            primes.append(n)
        for p in primes:
            meter.charge()
            if n*p > D:
                break
            least[n*p] = p
            if n % p == 0:
                mu[n*p] = 0
                break
            mu[n*p] = -mu[n]
    return mu


def evaluate(h, b, direct, den, R, u, v, mu, meter):
    # Dense kernel/suffix temporaries are prospectively bounded by source radius.
    require(128*(R+u+v+4) <= MAX_BYTES, 'evaluation scratch memory gate')
    kappa, kernel = [0]*(R+1), [0]*(R+1)
    hmap = dict(h)
    running = 0
    for n in range(R, 0, -1):
        meter.charge()
        running += hmap.get(n, 0)
        kappa[n] = running
    # K(t)=sum_k kappa(kt). This avoids enumerating h for every product.
    for t in range(1, R+1):
        meter.charge(R//t)
        kernel[t] = sum(kappa[t::t])
    def moment(cut):
        result = Q(0)
        for a in range(1, cut+1):
            meter.charge(1 + a.bit_length() + result.denominator.bit_length())
            result = bounded(result + Q(mu[a], a))
        return result
    H_u, H_v = moment(u), moment(v)
    L_u = sum(mu[a]*kappa[a] for a in range(1, u+1))
    L_v = sum(mu[a]*kappa[a] for a in range(1, v+1))
    bilinear_kernel = 0
    for a in range(1, u+1):
        for z in range(1, v+1):
            meter.charge(1 + (a*z).bit_length())
            # Retain units, common primes, repeated primes and products above R.
            t = a*z
            bilinear_kernel += mu[a]*mu[z]*(kernel[t] if t <= R else 0)
    # The complete reciprocal rectangle equals H_u*H_v, including t>R.
    # Its subtraction retains precisely those nonzero residual terms.
    E = bounded(bilinear_kernel - b*H_u*H_v)
    J = bounded(L_u + L_v - E)
    separable = bounded(-b*H_u*H_v)
    actual = bounded(direct + separable + J)
    independent = direct + sum(mu[n]*kappa[n] for n in range(1, R+1))
    meter.charge(R)
    require(actual == independent, 'complete joined Mobius identity mismatch')
    values = dict(H_u=H_u, H_v=H_v, L_u=Q(L_u), L_v=Q(L_v), E=E,
                  J=J, separable=separable, direct=Q(direct), actual_coefficient=actual)
    return dict(u=u, v=v, **{name: qtext(bounded(value if name in ('H_u', 'H_v') else value/den))
                            for name, value in values.items()})


def verify_source(cert, meter=None):
    meter = Meter() if meter is None else meter
    input_bytes = scan(cert, meter)
    keys(cert, 'schema N y max_j parameters programs endpoints ' + ' '.join(FLAGS), 'source')
    require(cert['schema'] == 'mobius-moment-scale-source-v1', 'source schema')
    flags(cert)
    p, q = parameters(cert['parameters'], meter)
    N = integer(cert['N'], 2, 65_536)
    D = 4*N//p
    y = integer(cert['y'], 1, D)
    max_j = integer(cert['max_j'], 0, min(D, 4096))
    require(input_bytes + 2048*(D+2) + 2048*max_j*128 <= MAX_BYTES, 'checker prospective 2GiB expansion gate')
    retained_bytes = input_bytes + 2048*(D+2)
    require(type(cert['programs']) is list and 1 <= len(cert['programs']) <= 128, 'complete bounded program list')
    derivations = [_program(program, meter)[1] for program in cert['programs']]
    require(type(cert['endpoints']) is list and len(cert['endpoints']) == 2, 'both ordered endpoints')
    # Geometry is regenerated before the evaluator queries any arithmetic signs.
    regenerated = []
    for endpoint, ratio in zip(cert['endpoints'], (Q(p, q), Q(1))):
        keys(endpoint, 'ratio denominator steps M1_scaled rows', 'endpoint')
        require(rational(endpoint['ratio']) == ratio, 'ordered endpoint ratio')
        den, num = ratio.denominator, ratio.numerator
        integer(endpoint['denominator'], den, den)
        def W(b, d):
            return 4*N//(b*d) - 3*(2*N//(b*d)) + 2*(N//(b*d))
        g = [0]*(D+2)
        for d in range(y+1, D+1):
            meter.charge(12)
            g[d] = -(den*W(p, d)-num*W(q, d))
        steps = [[t, g[t]-g[t+1]] for t in range(1, D+1) if g[t] != g[t+1]]
        require(sparse(endpoint['steps'], D, meter) == steps, 'joined source steps mismatch')
        integer(endpoint['M1_scaled'], 0)
        require(endpoint['M1_scaled'] == sum(abs(a)*t for t, a in steps), 'joined M1 mismatch')
        require(type(endpoint['rows']) is list and len(endpoint['rows']) == max_j, 'complete row count')
        atoms = {}
        for b, scale in ((p, den), (q, -num)):
            for factor, weight in ((4, 1), (2, -3), (1, 2)):
                z = factor*N//b
                atoms[z] = atoms.get(z, 0) + scale*weight
        regen_rows = []
        for j, row in enumerate(endpoint['rows'], 1):
            keys(row, 'j R direct_scaled prefix_steps b_scaled V_scaled plans', 'row')
            R = D//j
            integer(row['j'], j, j)
            integer(row['R'], R, R)
            direct = atoms.get(j, 0)
            integer(row['direct_scaled'])
            require(row['direct_scaled'] == direct, 'coalesced direct atoms mismatch')
            hmap = {}
            for t, a in steps:
                meter.charge(4)
                for A, sign in ((t//j, 1), (t//(j+1), -1)):
                    if A:
                        hmap[A] = hmap.get(A, 0)+sign*a
            h = [[A, value] for A, value in sorted(hmap.items()) if value]
            require(sparse(row['prefix_steps'], R, meter) == h, 'joined prefix steps mismatch')
            b = sum(A*value for A, value in h)
            V = sum(abs(value) for _, value in h)
            integer(row['b_scaled'])
            integer(row['V_scaled'], 0)
            require(row['b_scaled'] == b and row['V_scaled'] == V, 'joined b/V mismatch')
            require(type(row['plans']) is list and len(row['plans']) == sum(d is not None for d in derivations), 'complete derived plans')
            pairs = []
            plan_iterator = iter(row['plans'])
            for program_index, d in enumerate(derivations):
                if d is None:
                    continue
                plan = next(plan_iterator)
                keys(plan, 'program_index u v T_u T_v strict_rank universal_base_gate short_zero_support', 'plan')
                theta, gu, gv, exposure = (rational(d[name]) for name in ('theta', 'gamma_u', 'gamma_v', 'exposure'))
                u, v = floor_power(R, theta, meter), floor_power(R, 1-theta, meter)
                Tu, Tv = ceil_power(R, gu, meter), ceil_power(R, gv, meter)
                integer(plan['program_index'], program_index, program_index)
                for name, value in (('u', u), ('v', v), ('T_u', Tu), ('T_v', Tv)):
                    integer(plan[name], value, value)
                require((u+1)*(v+1) > R and Tu >= u and Tv >= v, 'complete rectangle/domain gate')
                beta = 1-exposure
                universal = R >= 3 and power(R, beta.numerator, meter) >= power(2, beta.denominator, meter)
                for name, value in (('strict_rank', max(Tu, Tv) < R),
                                    ('universal_base_gate', universal), ('short_zero_support', (j+1)*max(u, v) <= y)):
                    require(plan[name] is value, 'truthful finite plan gate '+name)
                if (u, v) not in pairs:
                    pairs.append((u, v))
            retained_bytes += 1024 + 320*len(h) + 256*len(pairs)
            require(retained_bytes <= MAX_BYTES, 'checker retained geometry 2GiB gate')
            regen_rows.append((j, R, h, b, direct, pairs))
        regenerated.append((str(ratio), den, regen_rows))
    mu = ordinary_mu(D, meter)
    mu_prefix = [0]*(D+1)
    for n in range(1, D+1):
        meter.charge()
        mu_prefix[n] = mu_prefix[n-1]+mu[n]
    endpoints = []
    for ratio, den, rows in regenerated:
        checked = []
        for j, R, h, b, direct, pairs in rows:
            evaluations = []
            for u, v in pairs:
                # A maximal100000-bit rational emits fewer than61000 characters.
                # Reserve scratch and a full next evaluation before creating it.
                require(retained_bytes + 128*(R+u+v+4) + 4_000_000 <= MAX_BYTES,
                        'checker prospective evaluation/output 2GiB gate')
                evaluation = evaluate(h, b, direct, den, R, u, v, mu, meter)
                retained_bytes += 2048 + sum(4*len(value) for value in evaluation.values() if type(value) is str)
                evaluations.append(evaluation)
            # Rows with no derived plan still have an independently evaluated coefficient.
            actual = Q(direct + sum(value*mu_prefix[A] for A, value in h), den)
            meter.charge(len(h))
            require(all(e['actual_coefficient'] == qtext(actual) for e in evaluations), 'independent source coefficient mismatch')
            checked.append(dict(j=j, R=R, actual_coefficient=qtext(actual), evaluations=evaluations))
        endpoints.append(dict(ratio=ratio, rows=checked))
    return dict(verified=True, N=N, y=y, max_j=max_j, endpoints=endpoints, **{f: False for f in FLAGS})
