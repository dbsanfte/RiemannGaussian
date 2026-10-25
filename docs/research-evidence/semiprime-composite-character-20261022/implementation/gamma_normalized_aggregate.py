"""Paid original-gamma normalized Gauss unit aggregates, not a locator.

Input t is a supplied public unit; gamma=t², with no root-extraction oracle.
Imports reviewed aggregate code and frozen PackedGauss without modifying them.
"""
import argparse
import json
from math import gcd
from composite_gauss_aggregate import acquire, load_packed, power, rho, d_power


def scale(a, scalar, N):
    return [(scalar*x) % N for x in a]


def ce_inverse(pg, exponent, coefficients=None):
    """Actual packed C_E inverse for ODD order, including all exponent cases."""
    if pg.k % 2 == 0:
        raise ValueError('C_E norm inverse requires odd character order')
    if exponent < 0:
        raise ValueError('nonnegative E required by packed quotient acquisition')
    CE = pg.quotient(exponent) if coefficients is None else coefficients
    if len(CE) != pg.k:
        raise ValueError('C_E length must equal character order')
    E0 = [pow(pg.k, -1, pg.N)]*pg.k
    projector = pg.projector(exponent)
    DE = [((1-pg.ell)*x + (pg.ell if i == 0 else 0)) % pg.N
          for i, x in enumerate(projector)]
    return pg.mul(pg.mul(rho(CE, -1), DE),
                  d_power(pg.N, pg.ell, E0, -exponent))


def acquire_normalized(N, ell, m, t, repo_root, backend='packed'):
    if N < 3 or N % 2 == 0:
        raise ValueError('odd composite N required')
    t %= N
    g = gcd(t, N)
    if 1 < g < N:
        return dict(status='PUBLIC_FACTOR', factor=g, source='gcd(t,N)')
    if g == N:
        return dict(status='SATURATED_PUBLIC_UNIT', gcd=N,
                    reason='t is zero modulo N; supplied-unit contract fails')
    base = acquire(N, ell, m, repo_root, backend)
    if base['status'] != 'AGGREGATE':
        return base
    frozen = load_packed(repo_root)
    pg = frozen.PackedGauss(N, ell, m, backend)
    gamma = t*t % N
    V = scale(pg.mul(pg.mul(base['U'], base['U']),
                     d_power(N, ell, base['E0'], -m)), pow(t, m, N), N)
    V_inverse = scale(rho(V, -1), pow(gamma, -m, N), N)
    qh = power(pg, V, m)
    qh_inverse = scale(rho(qh, -1), pow(gamma, -m*m, N), N)
    W = [pg.one(), qh_inverse, pg.mul(qh_inverse, qh_inverse)]
    pairs = [dict(j=p['j'], opposite=p['opposite'], a=p['a'], s=p['s'],
                  scalar=pow(gamma, N+p['a'], N)) for p in base['pairs']]
    A, S, h = base['A'], base['S'], base['h']
    whole = scale(power(pg, qh_inverse, S), pow(gamma, A+N*h, N), N)
    weighted_A = power(pg, scale(V, pow(gamma, -1, N), N), A)
    return dict(status='NORMALIZED_AGGREGATE', N=N, ell=ell, m=m, t=t,
                gamma=gamma, A=A, S=S, h=h, V=V, V_inverse=V_inverse,
                qh=qh, qh_inverse=qh_inverse, W=W, pairs=pairs,
                whole=whole, weighted_A=weighted_A,
                counts=dict(shared_pair_vectors=3, expanded_pair_vectors=0,
                            normalized_output_vectors=9,
                            unit_rows=2*h, pair_descriptors=h,
                            base_jacobi_histograms=base['counts']['jacobi_histograms'],
                            base_cyclic_multiplications=base['counts']['cyclic_multiplications'],
                            normalized_cyclic_multiplications=pg.multiplications),
                scope='normalized unit aggregates only; no H/difference/locator acquisition')


def expand_normalized_pair_for_test(result, descriptor):
    return scale(result['W'][descriptor['s']], descriptor['scalar'], result['N'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('N','ell','m','t'):
        parser.add_argument('--'+name, type=int, required=True)
    parser.add_argument('--repo-root', required=True)
    args = parser.parse_args()
    print(json.dumps(acquire_normalized(args.N,args.ell,args.m,args.t,args.repo_root),
                     sort_keys=True))
