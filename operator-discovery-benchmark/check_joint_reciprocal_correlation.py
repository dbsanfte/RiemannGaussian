"""Independent direct-convolution source and joined reciprocal correlation.

O is evaluated from reciprocal intervals plus the complete high triangle,
never as energy minus a product head and diagonal. All signed crosses and
exact-to-power center corrections remain explicit. Finite checks prove no
uniform source bound or RH theorem.
"""
from math import isqrt
from flint import arb, ctx

MAX_HORIZON = 131071
POWER_WORK = 64
ZETA_WORK = 256


def _precision():
    if ctx.prec != 192: raise ValueError('independent audit Arb precision192 required')


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb enclosure')
    return value


def _sieves(H, meter):
    mu = [1] * (H + 1); mu[0] = 0
    composite = [False] * (H + 1); prime_power = [False] * (H + 1)
    meter.charge(3 * (H + 1))
    for p in range(2, H + 1):
        meter.charge()
        if composite[p]: continue
        for n in range(p, H + 1, p):
            meter.charge(2); mu[n] = -mu[n]
            if n != p: composite[n] = True
        for n in range(p * p, H + 1, p * p): meter.charge(); mu[n] = 0
        power = p
        while power <= H:
            prime_power[power] = True; meter.charge(2); power *= p
    return mu, prime_power


class State(dict):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._prefixes = None


def source(H, meter):
    _precision()
    if type(H) is not int or not 1 <= H <= MAX_HORIZON: raise ValueError('strictH1..131071')
    meter.live(32 * (H + 1) + 4096)
    mu, prime_power = _sieves(H, meter)
    roots = [arb(0)] * (H + 1); u = [arb(0)] * (H + 1); v = [arb(0)] * (H + 1)
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
            B[d * k] = _finite(B[d * k] + _finite(au[d] * av[k], meter), meter); meter.charge(2)
    p = [arb(0)] * (H + 1); overlap = [arb(0)] * (H + 1); a = [arb(0)] * (H + 1)
    beta = arb(9) / 2; meter.charge(2)
    for n in range(2, H + 1):
        p[n] = _finite(beta * (B[n] - au[n] - av[n]), meter); meter.charge(3)
        if prime_power[n]: overlap[n] = p[n]
        else: a[n] = p[n]
    meter.charge(3 * ZETA_WORK + 7)
    z = _finite((arb(2) / 3).zeta(), meter); w = _finite((arb(4) / 3).zeta(), meter)
    z_u = _finite((arb(1) / 3).zeta(), meter)
    if z.contains(0): raise ArithmeticError('zeta(2/3) denominator separated fromzero')
    m = _finite(arb(27) / 4 * (w / (z * z) - 1 / z), meter); meter.charge(6)
    R_u = _finite(arb(2) / 3 * m, meter); meter.charge(2)
    E0 = _finite(-R_u * z_u, meter)
    R = [arb(0)] * (H + 1); t = [arb(0)] * (H + 1); T = [arb(0)] * (H + 1)
    error = [arb(0)] * (H + 1); power_center = [arb(0)] * (H + 1)
    A = cumulative_u = prefix = arb(0)
    for n in range(1, H + 1):
        power_center[n] = _finite(R_u * u[n], meter)
        t[n] = _finite(a[n] - power_center[n], meter)
        prefix = _finite(prefix + t[n], meter); T[n] = prefix
        A = _finite(A + a[n], meter)
        main = _finite(m * _finite(roots[n] * roots[n], meter), meter)
        R[n] = _finite(A - main, meter)
        cumulative_u = _finite(cumulative_u + u[n], meter)
        error[n] = _finite(main - _finite(R_u * cumulative_u, meter), meter)
    return State(H=H, precision=192, a=a, au=au, av=av, p=p, d=overlap,
                 R=R, tilde_b=t, tilde_R=T, mu=mu, m=m, R_u=R_u, E0=E0,
                 center_error=error, prime_power=prime_power, power_center=power_center, m_u=m)


def _prepare(state, meter):
    if state._prefixes is not None:
        if state._prefixes['meter'] is not meter: raise ValueError('one shared cache work meter required')
        return state._prefixes
    H = state['H']; meter.live(32 * (H + 1) + 4096)
    Q = [arb(0)] * (H + 1); Q1 = [arb(0)] * (H + 1)
    A = [arb(0)] * (H + 1); C = [arb(0)] * (H + 1)
    Qa = [arb(0)] * (H + 1); Qc = [arb(0)] * (H + 1); Qac = [arb(0)] * (H + 1)
    prefix = arb(0)
    for n in range(1, H + 1):
        # Bind the complete supplied prefix even for adversarial synthetic rows.
        prefix = _finite(prefix + state['tilde_b'][n], meter)
        if not prefix.overlaps(state['tilde_R'][n]): raise ValueError('tilde prefix does not match full coefficients')
        raw, center = state['a'][n], state['power_center'][n]
        if not _finite(raw - center, meter).overlaps(state['tilde_b'][n]): raise ValueError('raw/power center coefficient binding')
        A[n] = _finite(A[n - 1] + raw, meter); C[n] = _finite(C[n - 1] + center, meter)
        Qa[n] = _finite(Qa[n - 1] + _finite(raw * raw, meter), meter)
        Qc[n] = _finite(Qc[n - 1] + _finite(center * center, meter), meter)
        Qac[n] = _finite(Qac[n - 1] + _finite(raw * center, meter), meter)
        square = _finite(state['tilde_b'][n] ** 2, meter)
        Q[n] = _finite(Q[n - 1] + square, meter)
        Q1[n] = _finite(Q1[n - 1] + _finite(n * square, meter), meter)
    state._prefixes = dict(meter=meter, Q=Q, Q1=Q1, A=A, C=C, Qa=Qa, Qc=Qc, Qac=Qac)
    return state._prefixes


def query(X, state, meter):
    _precision()
    if type(X) is not int or X < 1 or not isinstance(state, State) or state.get('precision') != 192:
        raise ValueError('positive integerX and own192-bit State required')
    H = state.get('H'); N = 2 * X - 1
    if type(H) is not int or not 1 <= H <= MAX_HORIZON or N > H: raise ValueError('complete2X-1 source horizon required')
    for key in ('tilde_b', 'tilde_R', 'R', 'a', 'power_center'):
        if type(state.get(key)) is not list or len(state[key]) != H + 1:
            raise ValueError('complete source/prefix dimensions')
        if not state[key][0].is_zero(): raise ValueError('indexzero must vanish')
    prepared = _prepare(state, meter); Q, Q1 = prepared['Q'], prepared['Q1']
    t, T, R = state['tilde_b'], state['tilde_R'], state['R']; c = isqrt(X)
    meter.live(32 * (H + 1) + 4096)
    A, C, Qa, Qc, Qac = (prepared[key] for key in ('A', 'C', 'Qa', 'Qc', 'Qac'))
    sum_A = sum_C = tri_aa = tri_mm = tri_cross = arb(0)
    sum_T = high_square = high_diagonal_triangle = energy_R = energy_T = cross = error_square = arb(0)
    for n in range(X, N + 1):
        sum_A = _finite(sum_A + A[n], meter); sum_C = _finite(sum_C + C[n], meter)
        high_a = _finite(A[n] - A[c], meter); high_c = _finite(C[n] - C[c], meter)
        tri_aa = _finite(tri_aa + _finite(high_a * high_a - (Qa[n] - Qa[c]), meter), meter); meter.charge(2)
        tri_mm = _finite(tri_mm + _finite(high_c * high_c - (Qc[n] - Qc[c]), meter), meter); meter.charge(2)
        tri_cross = _finite(tri_cross - _finite(2 * (high_a * high_c - (Qac[n] - Qac[c])), meter), meter); meter.charge(3)
        sum_T = _finite(sum_T + T[n], meter)
        high = _finite(T[n] - T[c], meter)
        high_square = _finite(high_square + _finite(high * high, meter), meter)
        high_diagonal_triangle = _finite(high_diagonal_triangle + _finite(Q[n] - Q[c], meter), meter)
        energy_R = _finite(energy_R + _finite(R[n] * R[n], meter), meter)
        energy_T = _finite(energy_T + _finite(T[n] * T[n], meter), meter)
        error = _finite(T[n] - R[n], meter)
        cross = _finite(cross - _finite(2 * T[n] * error, meter), meter); meter.charge()
        error_square = _finite(error_square + _finite(error * error, meter), meter)
    reciprocal = low = rec_aa = rec_mm = rec_cross = arb(0)
    for h in range(1, c + 1):
        endpoint = X // h; meter.charge()
        raw_interval = _finite(sum_A - X * A[endpoint], meter); meter.charge()
        center_interval = _finite(sum_C - X * C[endpoint], meter); meter.charge()
        raw, center = state['a'][h], state['power_center'][h]
        rec_aa = _finite(rec_aa + raw * raw_interval, meter); meter.charge()
        rec_mm = _finite(rec_mm + center * center_interval, meter); meter.charge()
        rec_cross = _finite(rec_cross - (raw * center_interval + center * raw_interval), meter); meter.charge(3)
        interval_sum = _finite(sum_T - _finite(X * T[endpoint], meter), meter)
        reciprocal = _finite(reciprocal + _finite(t[h] * interval_sum, meter), meter)
        low = _finite(low + _finite(t[h] * T[endpoint], meter), meter)
    denominator = X * X; meter.charge()
    reciprocal = _finite(2 * reciprocal / denominator, meter); meter.charge()
    triangle_square = _finite(high_square / denominator, meter)
    triangle_diagonal = _finite(high_diagonal_triangle / denominator, meter)
    triangle = _finite(triangle_square - triangle_diagonal, meter)
    O = _finite(reciprocal + triangle, meter)
    low_head = _finite((2 * low - T[c] * T[c]) / X, meter); meter.charge(3)
    high_diagonal = _finite((X * (Q[X] - Q[c]) + 2 * X * (Q[N] - Q[X]) - (Q1[N] - Q1[X])) / denominator, meter); meter.charge(8)
    energy_R = _finite(energy_R / denominator, meter); energy_T = _finite(energy_T / denominator, meter)
    center_cross = _finite(cross / denominator, meter); center_square = _finite(error_square / denominator, meter)
    center_correction = _finite(center_cross + center_square, meter)
    residual = _finite(energy_R - O - low_head - high_diagonal - center_correction, meter); meter.charge(4)
    O_aa = _finite((2 * rec_aa + tri_aa) / denominator, meter); meter.charge(2)
    O_mm = _finite((2 * rec_mm + tri_mm) / denominator, meter); meter.charge(2)
    O_cross = _finite((2 * rec_cross + tri_cross) / denominator, meter); meter.charge(2)
    sector_residual = _finite(O - O_aa - O_cross - O_mm, meter); meter.charge(2)
    return dict(X=X, Hsplit=c, N=N, O=O, reciprocal=reciprocal, triangle=triangle,
                O_aa=O_aa, O_cross=O_cross, O_mm=O_mm, sector_residual=sector_residual,
                triangle_square=triangle_square, triangle_diagonal=triangle_diagonal,
                low_head=low_head, high_diagonal=high_diagonal,
                energy_R=energy_R, energy_tilde=energy_T,
                center_cross=center_cross, center_square=center_square,
                center_correction=center_correction, identity_residual=residual,
                uniform_signed_bound_proved=False, RH_proved=False,
                independent_signed_gain_proved=False)
