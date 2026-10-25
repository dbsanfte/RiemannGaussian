"""Public composite square-colour metadata; no hidden factors or long H inputs."""
from math import gcd, isqrt
import argparse
import json


def ceil_sixth_root(N):
    if N < 1:
        raise ValueError('positive integer required')
    lo, hi = 0, 1 << ((N.bit_length()+5)//6)
    while hi-lo > 1:
        mid = (lo+hi)//2
        if mid**6 < N:
            lo = mid
        else:
            hi = mid
    return hi


def sieve(limit):
    flags = bytearray(b'\x01')*(limit+1)
    flags[:2] = b'\x00\x00'
    for p in range(2, isqrt(limit)+1):
        if flags[p]:
            start = p*p
            flags[start:limit+1:p] = b'\x00'*((limit-start)//p+1)
    return flags


def auxiliary_prime(N):
    """First ell>2*ceil(N**(1/6)), ell=3 mod4, via doubling sieves."""
    threshold = 2*ceil_sixth_root(N)
    limit = max(8, 2*threshold)
    rounds = 0
    while True:
        flags = sieve(limit)
        rounds += 1
        for ell in range(threshold+1, limit+1):
            if ell % 4 == 3 and flags[ell]:
                return ell, {'sieve_limit': limit, 'sieve_rounds': rounds,
                             'threshold': threshold}
        limit *= 2


def factor_prime_powers(m):
    if m < 1:
        raise ValueError('positive modulus required')
    left, out, p = m, [], 2
    while p*p <= left:
        if left % p == 0:
            e, n = 0, 1
            while left % p == 0:
                left //= p
                e += 1
                n *= p
            out.append((p,e,n))
        p += 1 if p == 2 else 2
    if left > 1:
        out.append((left,1,left))
    return out


def screen_public_primes(N, ell, factors):
    """Individual screens: combined gcd may be N although each is proper."""
    records = []
    for p in sorted({ell, *(p for p,e,n in factors)}):
        g = gcd(N,p)
        records.append({'prime': p, 'gcd': g})
        if 1 < g < N:
            return {'status': 'FACTOR', 'factor': g, 'screens': records}
        if g == N:
            return {'status': 'INPUT_EQUALS_PUBLIC_PRIME', 'prime': p,
                    'screens': records}
    return {'status': 'COPRIME', 'screens': records}


def legendre_unit(a,p):
    v = pow(a % p, (p-1)//2, p)
    if v == 0:
        raise ValueError('Legendre input must be a unit')
    return 1 if v == 1 else -1


def catalog(m):
    """Explicit lists, total CRT work proportional to coloured output size."""
    if m < 3 or m % 2 == 0:
        raise ValueError('odd m>=3 required')
    factors = factor_prime_powers(m)
    partial = [((),0)]
    modulus, crt_pairs, local_scans = 1, 0, 0
    local_sizes = []
    for p,e,n in factors:
        marks = bytearray(n)
        for t in range(n):
            marks[t*t % n] = 1
        squares = [r for r in range(n) if marks[r]]
        nu = next(a for a in range(1,p) if legendre_unit(a,p) == -1)
        minus = [(nu*r) % n for r in squares]
        local = [(1,r) for r in squares]+[(-1,r) for r in minus]
        inv = pow(modulus,-1,n)
        following = []
        for colour,r in partial:
            for sign,s in local:
                z = r+modulus*((s-r)*inv % n)
                following.append((colour+(sign,),z))
                crt_pairs += 1
        partial = following
        modulus *= n
        local_scans += n
        local_sizes.append({'prime_power': n, 'square_count': len(squares),
                            'coloured_count': len(local)})
    palettes = {}
    for colour,r in partial:
        palettes.setdefault(colour,[]).append(r)
    for values in palettes.values():
        values.sort()
    return {'m': m, 'factorization': factors, 'palettes': palettes,
            'total_descriptors': len(partial), 'colour_count': len(palettes),
            'local_sizes': local_sizes, 'local_scans': local_scans,
            'crt_pair_visits': crt_pairs}


def canonical_rows(N,m):
    if m < 3 or m % 2 == 0 or gcd(N,m) != 1:
        raise ValueError('odd m>=3 coprime to N required')
    primes = [p for p,e,n in factor_prime_powers(m)]
    rows = []
    for j in range(1,m):
        if gcd(j,m) != 1:
            continue
        inv = pow(j,-1,m)
        a = N*inv*inv % m
        b = (((a*j*j-N)//m)*inv) % m
        if b > m//2:
            b -= m
        numerator = N+j*m*b-j*j*a
        assert numerator % (m*m) == 0
        c = numerator//(m*m)
        ell = m*b-2*a*j
        Delta = b*b-4*a*c
        inv4aj = pow(4*a*j,-1,m)
        kappa = -Delta*inv4aj % m
        v = ell-m*m*kappa
        E = N+a+ell
        assert (v*v-4*a*N) % (m**3) == 0
        rows.append({'j': j, 'a': a, 'b': b, 'c': c, 'ell': ell,
                     'Delta': Delta, 'kappa': kappa, 'v': v, 'E': E,
                     'e': E-m*m*kappa,
                     'colour': tuple(legendre_unit(inv4aj,p) for p in primes)})
    return rows


def preprocess(N):
    if N < 3 or N % 2 == 0:
        raise ValueError('odd N>=3 required; semiprimality is not certified')
    ell, selection = auxiliary_prime(N)
    m = (ell-1)//2
    factors = factor_prime_powers(m)
    screened = screen_public_primes(N,ell,factors)
    result = {'N': N, 'ell': ell, 'm': m, 'selection': selection,
              'screen': screened}
    if screened['status'] != 'COPRIME':
        return result
    cat = catalog(m)
    rows = canonical_rows(N,m)
    result.update({'catalog': cat, 'rows': rows,
                   'ledger': {'row_count': len(rows),
                              'palette_residue_count': cat['total_descriptors'],
                              'colour_count': cat['colour_count'],
                              'crt_pair_visits': cat['crt_pair_visits'],
                              'local_square_scan_count': cat['local_scans'],
                              'long_H_values_computed': 0}})
    return result


def jsonable(result):
    out = dict(result)
    if 'catalog' in out:
        cat = dict(out['catalog'])
        cat['palettes'] = [{'colour': colour, 'residues': values}
                           for colour,values in sorted(cat['palettes'].items())]
        out['catalog'] = cat
    return out


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('N',type=int)
    args = parser.parse_args()
    try:
        print(json.dumps(jsonable(preprocess(args.N)),sort_keys=True))
    except ValueError as exc:
        parser.error(str(exc))
