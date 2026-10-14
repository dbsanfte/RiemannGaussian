"""Independent annular cell means, full storage, and paid local detail.

Complete source histories enter prepare; no prefix resets at cell boundaries.
Coarse+detail is an exact variance identity. The path majorant is derived from
all within-cell increments, not inferred from an observed ratio. The analytic
payment is conditional on independently verified actual-source majorants and
never establishes the full coarse storage bound.
"""
from copy import deepcopy
from fractions import Fraction as Q
import re
from flint import arb, ctx
from check_core_control_synthesis import validate as validate_storage

MAX_HORIZON = 524287
SCALAR_BITS = 4096


def _rational(text, meter):
    if type(text) is not str or not 1 <= len(text) <= 2500 or re.fullmatch(r'-?\d+(?:/\d+)?', text) is None:
        raise ValueError('bounded canonical rational string')
    meter.charge(len(text) + 1)
    try: value = Q(text)
    except (ValueError, ZeroDivisionError) as error: raise ValueError('rational string') from error
    if str(value) != text or max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > SCALAR_BITS:
        raise ValueError('canonical bounded rational')
    return value


def _finite(value, meter):
    meter.charge()
    if type(value) is not arb or not value.is_finite(): raise ArithmeticError('finite Arb value')
    return value


def _real(value, meter):
    meter.charge(2)
    return _finite(arb(value.numerator) / value.denominator, meter)


def _precision():
    if ctx.prec != 192: raise ValueError('independent Arb precision192')


def _mesh(text, meter):
    value = _rational(text, meter)
    if not 0 < value <= 1: raise ValueError('mesh power in(0,1]')
    return value


def prepare(state, program, meter):
    validate_storage(program, meter); _precision()
    if type(state) is not dict or type(state.get('H')) is not int or not 1 <= state['H'] <= MAX_HORIZON:
        raise ValueError('complete explicit state horizon')
    H = state['H']
    for key in ('g', 'G', 'Bg', 'D'):
        values = state.get(key)
        if type(values) is not list or len(values) != H + 1 or not _finite(values[0], meter).is_zero():
            raise ValueError('complete zero-based source histories')
        for value in values[1:]: _finite(value, meter)
    meter.live(64 * (H + 1) + 4096)
    mix = _real(_rational(program['mix'], meter), meter)
    weight = _real(_rational(program['reserve'], meter), meter)
    auxiliary = program['auxiliary']; alpha = Q(0) if auxiliary is None else _rational(auxiliary['alpha'], meter)
    exponent = _real(-alpha, meter) if alpha else None
    U = [arb(0)] * (H + 1); auxiliary_values = [arb(0)] * (H + 1)
    for n in range(1, H + 1):
        value = arb(0)
        if auxiliary is not None:
            kind = auxiliary['kind']
            if kind == 'log_bank':
                meter.charge(64); logarithm = _finite(arb(2 * n).log(), meter)
                value = _finite(state['Bg'][n] / logarithm, meter)
            elif kind == 'half_delay': value = state['G'][n // 2]
            else: value = state['D'][n]
            if exponent is not None:
                meter.charge(64); value = _finite(value * _finite(arb(n) ** exponent, meter), meter)
        auxiliary_values[n] = value
        U[n] = _finite(state['G'][n] + _finite(mix * value, meter), meter)
    return dict(H=H, U=U, Q=auxiliary_values, weight=weight, program=deepcopy(program),
                coefficient_majorant_premise_verified=False)


def project(prepared, X, mesh_power, meter):
    _precision(); r = _mesh(mesh_power, meter)
    if type(X) is not int or X < 1 or X & (X - 1): raise ValueError('strict positive dyadicX')
    if type(prepared) is not dict or type(prepared.get('H')) is not int or not 1 <= prepared['H'] <= MAX_HORIZON:
        raise ValueError('complete prepared horizon')
    H = prepared['H']
    if 2 * X - 1 > H: raise ValueError('complete annular support')
    for key in ('U', 'Q'):
        values = prepared.get(key)
        if type(values) is not list or len(values) != H + 1 or not _finite(values[0], meter).is_zero():
            raise ValueError('complete zero-based prepared arrays')
    weight = _finite(prepared.get('weight'), meter)
    if not weight > 0: raise ValueError('strictly positive storage weight')
    k = X.bit_length() - 1; L = 1 << (r.numerator * k // r.denominator); meter.charge(4)
    count = X // L; meter.live(64 * (H + 1) + 16 * count + 4096)
    cells = []; full = coarse = detail = path = arb(0)
    def energy(u, q):
        meter.charge(3)
        return _finite(_finite(u * u, meter) + _finite(weight * _finite(q * q, meter), meter), meter)
    for start in range(X, 2 * X, L):
        stop = start + L; sum_u = sum_q = arb(0)
        for n in range(start, stop):
            u = _finite(prepared['U'][n], meter); q = _finite(prepared['Q'][n], meter)
            sum_u = _finite(sum_u + u, meter); sum_q = _finite(sum_q + q, meter)
            full = _finite(full + energy(u, q), meter)
        mean_u = _finite(sum_u / L, meter); mean_q = _finite(sum_q / L, meter); meter.charge(2)
        cells.append(dict(start=start, stop=stop, U_mean=mean_u, Q_mean=mean_q))
        if L > 1:
            coarse = _finite(coarse + _finite(L * energy(mean_u, mean_q), meter), meter)
            for n in range(start, stop):
                u = _finite(prepared['U'][n] - mean_u, meter)
                q = _finite(prepared['Q'][n] - mean_q, meter)
                detail = _finite(detail + energy(u, q), meter)
            for t in range(1, L):
                n = start + t
                du = _finite(prepared['U'][n] - prepared['U'][n - 1], meter)
                dq = _finite(prepared['Q'][n] - prepared['Q'][n - 1], meter)
                multiplier = Q(t * (L - t), 2); meter.charge(3)
                path = _finite(path + _finite(_real(multiplier, meter) * energy(du, dq), meter), meter)
    denominator = X * X; meter.charge()
    full = _finite(full / denominator, meter)
    if L == 1:
        coarse = full; detail = arb(0); path = arb(0); residual = arb(0); comparison = 'pass'
    else:
        coarse = _finite(coarse / denominator, meter); detail = _finite(detail / denominator, meter)
        path = _finite(path / denominator, meter); residual = _finite(full - coarse - detail, meter)
        if not residual.contains(0): raise ArithmeticError('complete variance identity failed')
        comparison = 'pass' if detail <= path else 'fail' if detail > path else 'unresolved'; meter.charge(2)
    return dict(X=X, L=L, cell_means=cells, full_storage=full, coarse_storage=coarse,
                detail_storage=detail, path_bound=path, identity_residual=residual, path_comparison=comparison,
                coefficient_majorant_premise_verified=False, all_scale_storage_bound_proved=False,
                all_scale_target_bound_proved=False, RH_proved=False)


def certificate(program, mesh_power, meter):
    """Conditional analytic detail payment, independent of measured source data."""
    validate_storage(program, meter); r = _mesh(mesh_power, meter)
    auxiliary = program['auxiliary']; mix = _rational(program['mix'], meter); weight = _rational(program['reserve'], meter)
    K = Q(37, 2); alpha = Q(0) if auxiliary is None else _rational(auxiliary['alpha'], meter)
    if not 0 <= alpha <= Q(1, 3): raise ValueError('analytic auxiliary alpha0..1/3')
    b = Q(0) if auxiliary is None else 2 * alpha + (4 if auxiliary['kind'] == 'log_bank' else 0)
    C = 2 * K * K if auxiliary is None else 4 * K * K * (1 + (2 * mix * mix + weight) * (1 + b * b))
    power = 2 * r - 1; bounded = r < Q(1, 2); meter.charge(45)
    return dict(schema='core-increment-projection-v1', program=deepcopy(program), mesh_power=mesh_power,
                source_majorant_constant=str(K), coefficient_majorant_premise='For all integers n>=1, |g(n)| and |f(n)-g(n)| <= (37/2)*d2(n), for the independently verified fixed actual source and transport.',
                coefficient_majorant_premise_verified=False, auxiliary_variation_constant=str(b),
                detail_constant=str(C), detail_power=str(power), raw_log_degree=3,
                domain='every dyadic X>=1; full annular cells, original global histories and both storage components',
                cofinal_recovery=r <= Q(1, 2), bounded_detail=bounded,
                bounded_detail_constant=str(C * 96 / (1 - 2 * r) ** 3) if bounded else None,
                effective_detail_log_degree=0 if bounded else 3 if r == Q(1, 2) else None,
                all_scale_coarse_bound_proved=False, all_scale_storage_bound_proved=False,
                all_scale_target_bound_proved=False, RH_proved=False)
