"""Independent complete centered product-cutoff kernels in Arb arithmetic.

Actual coefficients are built by direct Mobius/divisor convolution. Prefix
queries replace pair scatter, including squarefree/coprime ordered supports.
Every restricted kernel retains all AA, center-cross and center-square terms.
"""
from fractions import Fraction as Q
from math import isqrt
from flint import arb, ctx

MAX_HORIZON = 2047
GAMMAS = ('0', '1/6', '1/3')
POWER_WORK = 64
ZETA_WORK = 256


def _precision():
    if ctx.prec not in (160, 192): raise ValueError('Arb precision160or192 required')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb value')
    return value


def _mobius(H, meter):
    mu = [1] * (H + 1); mu[0] = 0; prime = [True] * (H + 1)
    prime[0] = prime[1] = False; meter.charge(2 * (H + 1))
    for p in range(2, H + 1):
        meter.charge()
        if not prime[p]: continue
        for n in range(p, H + 1, p):
            meter.charge(2); mu[n] = -mu[n]
            if n != p: prime[n] = False
        for n in range(p * p, H + 1, p * p):
            meter.charge(); mu[n] = 0
    return mu


class State(dict):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._cache = {}; self._cache_cells = 0


def source(H, meter):
    _precision()
    if type(H) is not int or not 1 <= H <= MAX_HORIZON: raise ValueError('completeH1..2047')
    meter.live(24 * (H + 1) + 4096)
    mu = _mobius(H, meter); roots = [arb(0)] * (H + 1)
    u = [arb(0)] * (H + 1); v = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        meter.charge(POWER_WORK); roots[n] = _finite(arb(n).root(3), meter)
        u[n] = _finite(1 / roots[n], meter); v[n] = _finite(u[n] * u[n], meter)
    au = [arb(0)] * (H + 1); av = [arb(0)] * (H + 1)
    for d in range(1, H + 1):
        meter.charge()
        if not mu[d]: continue
        for k in range(1, H // d + 1):
            au[d * k] = _finite(au[d * k] + mu[d] * u[k], meter)
            av[d * k] = _finite(av[d * k] + mu[d] * v[k], meter)
            meter.charge(4)
    B = [arb(0)] * (H + 1)
    for d in range(1, H + 1):
        for k in range(1, H // d + 1):
            B[d * k] = _finite(B[d * k] + _finite(au[d] * av[k], meter), meter)
    beta = arb(9) / 2; meter.charge(2)
    p = [arb(0)] * (H + 1); a = [arb(0)] * (H + 1)
    for n in range(2, H + 1):
        p[n] = _finite(beta * (B[n] - au[n] - av[n]), meter); meter.charge(3)
        # Independent trial prime-power predicate, preserving all mixed repeats.
        residual = n; first = 0
        for d in range(2, isqrt(n) + 1):
            meter.charge()
            if n % d == 0: first = d; break
        if first:
            while residual % first == 0: residual //= first; meter.charge(2)
        a[n] = arb(0) if not first or residual == 1 else p[n]
    meter.charge(2 * ZETA_WORK + 5)
    z = _finite((arb(2) / 3).zeta(), meter); w = _finite((arb(4) / 3).zeta(), meter)
    if z.contains(0): raise ArithmeticError('zeta denominator separated fromzero')
    c = _finite(arb(27) / 4 * (w / (z * z) - 1 / z), meter); meter.charge(6)
    m = [arb(0)] * (H + 1); R = [arb(0)] * (H + 1)
    previous = prefix = arb(0)
    for n in range(1, H + 1):
        power = _finite(roots[n] * roots[n], meter)
        m[n] = _finite(c * _finite(power - previous, meter), meter)
        prefix = _finite(prefix + a[n] - m[n], meter); meter.charge()
        R[n] = prefix; previous = power
    return State(H=H, precision=ctx.prec, a=a, m=m, R=R, c=c, mu=mu,
                 squarefree=[bool(value) for value in mu], p=p, a_u=au, a_v=av)


def _prefix(values, meter, stride=1, squarefree=None):
    F = [arb(0)]; KF = [arb(0)]
    for n in range(stride, len(values), stride):
        value = values[n] if squarefree is None or squarefree[n] else arb(0)
        F.append(_finite(F[-1] + value, meter))
        KF.append(_finite(KF[-1] + _finite(n * value, meter), meter))
    return F, KF


def _kernel_sum(prefix, K, L, X, stride, meter):
    F, KF = prefix; middle = min(K, L)
    lo = middle // stride; hi = K // stride
    meter.charge(6)
    return _finite((2 * X - L) * F[lo] + 2 * X * (F[hi] - F[lo]) - (KF[hi] - KF[lo]), meter)


def _prepare(X, gamma, state, meter):
    key = (X, gamma); N = 2 * X - 1
    if key in state._cache:
        cached = state._cache[key]
        if cached['meter'] is not meter: raise ValueError('cache belongs to one shared work meter')
        return cached
    predicted = 10 * (N + 1)
    for d in range(1, N + 1):
        meter.charge()
        if state['mu'][d]: predicted += 5 * (N // d) + 4
    meter.live(24 * (state['H'] + 1) + state._cache_cells + predicted + 4096)
    wa = [arb(0)] * (N + 1); wm = [arb(0)] * (N + 1)
    for n in range(1, N + 1):
        if gamma == '0': weight = arb(1); meter.charge()
        else:
            meter.charge(POWER_WORK)
            root = _finite(arb(n).root(6 if gamma == '1/6' else 3), meter)
            weight = _finite(1 / root, meter)
        wa[n] = _finite(state['a'][n] * weight, meter)
        wm[n] = _finite(state['m'][n] * weight, meter)
    full_a = _prefix(wa, meter); full_m = _prefix(wm, meter)
    multiples = {}; divisor_rows = [[] for _ in range(N + 1)]
    for d in range(1, N + 1):
        if not state['mu'][d]: continue
        multiples[d] = (_prefix(wa, meter, d, state['squarefree']), _prefix(wm, meter, d, state['squarefree']))
        for h in range(d, N + 1, d):
            meter.charge(); divisor_rows[h].append(d)
    cells = 10 * (N + 1) + sum(4 * (N // d + 1) for d in multiples) + sum(map(len, divisor_rows))
    state._cache_cells += cells
    meter.live(24 * (state['H'] + 1) + state._cache_cells + 4096)
    cached = dict(meter=meter, wa=wa, wm=wm, full_a=full_a, full_m=full_m,
                  multiples=multiples, divisors=divisor_rows)
    state._cache[key] = cached
    return cached


def cutoff(X, T, gamma, state, meter):
    _precision()
    if type(X) is not int or X < 1 or type(T) is not int or T < 0 or type(gamma) is not str or gamma not in GAMMAS:
        raise ValueError('positive integerX/nonnegative integerT/canonicalgamma')
    if not isinstance(state, State) or state.get('precision') != ctx.prec:
        raise ValueError('own State at current precision required')
    H = state.get('H'); N = 2 * X - 1
    if type(H) is not int or not 1 <= H <= MAX_HORIZON or N > H:
        raise ValueError('complete product kernel support required')
    for key in ('a', 'm', 'mu', 'squarefree'):
        if type(state.get(key)) is not list or len(state[key]) != H + 1:
            raise ValueError('complete source dimensions')
    prepared = _prepare(X, gamma, state, meter)
    meter.live(24 * (H + 1) + state._cache_cells + 4096)
    aa = am = mm = aa_sf = am_sf = mm_sf = arb(0)
    for h in range(1, N + 1):
        K = min(N, T // h); L = max(X, h); meter.charge(4)
        if not K: continue
        A = _kernel_sum(prepared['full_a'], K, L, X, 1, meter)
        M = _kernel_sum(prepared['full_m'], K, L, X, 1, meter)
        ah, mh = prepared['wa'][h], prepared['wm'][h]
        aa = _finite(aa + _finite(ah * A, meter), meter)
        am = _finite(am + _finite(ah * M, meter), meter)
        mm = _finite(mm + _finite(mh * M, meter), meter)
        if not state['squarefree'][h]: continue
        sfA = sfM = arb(0)
        for d in prepared['divisors'][h]:
            Ap, Mp = prepared['multiples'][d]; sign = state['mu'][d]
            sfA = _finite(sfA + sign * _kernel_sum(Ap, K, L, X, d, meter), meter)
            sfM = _finite(sfM + sign * _kernel_sum(Mp, K, L, X, d, meter), meter)
            meter.charge(2)
        aa_sf = _finite(aa_sf + _finite(ah * sfA, meter), meter)
        am_sf = _finite(am_sf + _finite(ah * sfM, meter), meter)
        mm_sf = _finite(mm_sf + _finite(mh * sfM, meter), meter)
    denominator = X * X
    aa = _finite(aa / denominator, meter); aa_sf = _finite(aa_sf / denominator, meter)
    cross = _finite(-2 * am / denominator, meter); cross_sf = _finite(-2 * am_sf / denominator, meter)
    mm = _finite(mm / denominator, meter); mm_sf = _finite(mm_sf / denominator, meter)
    aa_ns = _finite(aa - aa_sf, meter); cross_ns = _finite(cross - cross_sf, meter); mm_ns = _finite(mm - mm_sf, meter)
    centered_sf = _finite(aa_sf + cross_sf + mm_sf, meter)
    centered_ns = _finite(aa_ns + cross_ns + mm_ns, meter)
    centered = _finite(centered_sf + centered_ns, meter); meter.charge(4)
    return dict(X=X, T=T, gamma=gamma, aa_sf=aa_sf, aa_ns=aa_ns,
                cross_sf=cross_sf, cross_ns=cross_ns, mm_sf=mm_sf, mm_ns=mm_ns,
                centered_sf=centered_sf, centered_ns=centered_ns, centered=centered,
                uniform_signed_bound_proved=False, RH_proved=False,
                centered_projection_positive_claimed=False)
