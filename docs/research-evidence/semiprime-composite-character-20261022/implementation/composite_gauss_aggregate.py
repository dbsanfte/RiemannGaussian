"""Reference paid whole-unit Gauss aggregate; no H/difference evaluator.

The frozen PackedGauss is loaded only from an explicit repository root.
Core inputs contain N, ell, m, not its hidden factors. All-pair vectors
remain represented by three W_s plus scalar/row descriptors.
"""
import argparse
import importlib.util
import json
from math import gcd
from pathlib import Path

FROZEN = Path('docs/research-evidence/semiprime-colour-retention-20261022/implementation/packed_gauss.py')


def load_packed(repo_root):
    path = Path(repo_root).resolve() / FROZEN
    spec = importlib.util.spec_from_file_location('frozen_packed_gauss', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rows(N, m):
    out = []
    for j in range(1, m):
        if gcd(j, m) != 1:
            continue
        ji = pow(j, -1, m)
        a = N * ji * ji % m
        b = ((a*j*j-N)//m) * ji % m
        if b > m//2:
            b -= m
        elltag = m*b-2*a*j
        out.append(dict(j=j, a=a, b=b, ell=elltag, E=N+a+elltag))
    return out


def power(pg, a, e):
    if e < 0:
        raise ValueError('power requires supplied inverse for negative exponent')
    ans = pg.one()
    while e:
        if e & 1:
            ans = pg.mul(ans, a)
        e >>= 1
        if e:
            a = pg.mul(a, a)
    return ans


def rho(a, j):
    m = len(a)
    if gcd(j, m) != 1:
        raise ValueError('character automorphism requires unit tag')
    out = [0]*m
    for i, v in enumerate(a):
        out[i*j % m] = v
    return out


def d_power(N, ell, E0, e):
    """D^e, including the exceptional trivial component, for signed e."""
    scalar = pow(ell, e, N)
    return [((1-scalar)*v + (scalar if i == 0 else 0)) % N
            for i, v in enumerate(E0)]


def acquire(N, ell, m, repo_root, backend='packed'):
    frozen = load_packed(repo_root)
    if N < 3 or N % 2 == 0:
        raise ValueError('odd composite N required')
    if m < 3 or m % 2 == 0 or (ell-1) % m:
        raise ValueError('odd m>=3 dividing ell-1 required')
    # Individual known PRIME screens cannot saturate on a composite N.
    screens = sorted(set(frozen.prime_factors(m) + [ell]))
    for p in screens:
        g = gcd(N, p)
        if 1 < g < N:
            return dict(status='PUBLIC_FACTOR', factor=g, screened_prime=p)
        if g == N:
            raise ValueError('N equals a screened prime; composite input contract fails')
    pg = frozen.PackedGauss(N, ell, m, backend)
    E0 = [pow(m, -1, N)]*m
    D = d_power(N, ell, E0, 1)
    D_inverse = d_power(N, ell, E0, -1)
    U = [(-x) % N for x in pg.quotient(m)]
    # U bar(U)=D^m in the WHOLE packed algebra, also at X=1.
    U_inverse = pg.mul(rho(U, -1), d_power(N, ell, E0, -m))
    W1 = power(pg, U_inverse, m)
    W = [pg.one(), W1, pg.mul(W1, W1)]
    unit_rows = rows(N, m)
    lookup = {r['j']: r for r in unit_rows}
    pairs = []
    A = S = 0
    for r in unit_rows:
        j = r['j']
        if j >= m-j:
            continue
        other = lookup[m-j]
        assert r['a'] == other['a']
        numerator = -r['ell']-other['ell']
        assert numerator % (m*m) == 0
        s = numerator//(m*m)
        assert s in (0, 1, 2)
        A += r['a']
        S += s
        pairs.append(dict(j=j, opposite=m-j, a=r['a'], s=s,
                          delta=pow(-1, s, N), scalar=pow(ell, r['a']+N, N)))
    h = len(pairs)
    whole = pg.mul(power(pg, W1, S), d_power(N, ell, E0, A+N*h))
    weighted_C = pg.mul(power(pg, U, A), d_power(N, ell, E0, -A))
    return dict(status='AGGREGATE', N=N, auxiliary_prime=ell, m=m,
                h=h, A=A, S=S, U=U, D=D, D_inverse=D_inverse, E0=E0,
                W=W, pairs=pairs, whole=whole, weighted_C=weighted_C,
                counts=dict(unit_rows=len(unit_rows), pair_descriptors=h,
                            shared_pair_vectors=3, packed_output_vectors=9,
                            expanded_pair_vectors=0,
                            jacobi_histograms=pg.histograms,
                            cyclic_multiplications=pg.multiplications),
                scope='unit aggregate and shared pairs only; no H/difference evaluation')


def expand_pair_for_test(result, descriptor):
    """TEST/one-selected-query helper; never used by aggregate acquisition."""
    N = result['N']
    e0 = result['E0']
    w = result['W'][descriptor['s']]
    delta, scalar = descriptor['delta'], descriptor['scalar']
    return [(delta*z+scalar*(v-delta*z)) % N for z, v in zip(e0, w)]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', required=True)
    parser.add_argument('--N', type=int, required=True)
    parser.add_argument('--ell', type=int, required=True)
    parser.add_argument('--m', type=int, required=True)
    args = parser.parse_args()
    print(json.dumps(acquire(args.N, args.ell, args.m, args.repo_root), sort_keys=True))
