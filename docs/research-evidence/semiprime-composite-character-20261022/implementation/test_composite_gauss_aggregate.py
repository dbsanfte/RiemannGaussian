"""Small exact convention/composite-component controls, not coverage evidence."""
import argparse
import json
from math import gcd, isqrt
from pathlib import Path
from composite_gauss_aggregate import acquire, expand_pair_for_test, load_packed, rows


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def field_primes(step):
    out = []
    t = 1
    while len(out) < 2:
        p = 1+t*step
        if prime(p):
            out.append(p)
        t += 1
    return out


def generator(p, frozen):
    factors = frozen.prime_factors(p-1)
    return next(g for g in range(2, p) if all(pow(g, (p-1)//d, p) != 1 for d in factors))


def evaluate(v, z, p):
    out = 0
    for c in reversed(v):
        out = (out*z+c) % p
    return out


def run(repo_root):
    frozen = load_packed(repo_root)
    counts = dict(parameter_cases=0, character_components=0, proper_divisor_components=0,
                  direct_pair_checks=0, direct_whole_checks=0, weighted_checks=0,
                  public_factor_checks=0, invalid_checks=0)
    degree = 0
    for m, ell in ((3, 7), (9, 19), (15, 31), (9, 37)):
        p, q = field_primes(m*ell)
        N = p*q
        result = acquire(N, ell, m, repo_root)
        assert result['status'] == 'AGGREGATE'
        assert result['counts']['expanded_pair_vectors'] == 0
        assert result['counts']['shared_pair_vectors'] == 3
        degree = max(degree, m-1)
        pg = frozen.PackedGauss(N, ell, m)
        unit_rows = rows(N, m)
        for field in (p, q):
            g = generator(field, frozen)
            zeta_m = pow(g, (field-1)//m, field)
            zeta_ell = pow(g, (field-1)//ell, field)
            for character in range(m):
                z = pow(zeta_m, character, field)
                # Direct sums in the full split joint additive/character algebra.
                gauss = []
                for tag in range(m):
                    gauss.append(sum(pow(z, tag*pg.logs[x], field)*pow(zeta_ell, x, field)
                                     for x in range(1, ell)) % field)
                assert all(gauss)
                targets = {}
                weighted = 1
                for row in unit_rows:
                    j, a = row['j'], row['a']
                    ji = pow(j, -1, m)
                    targets[j] = (pow(gauss[1], row['ell'], field)
                                  *pow(gauss[j], a, field)
                                  *pow(gauss[ji], N, field)) % field
                    cj = pow(gauss[1], j, field)*pow(gauss[j], -1, field) % field
                    weighted = weighted*pow(cj, a, field) % field
                whole = 1
                for value in targets.values():
                    whole = whole*value % field
                assert evaluate(result['whole'], z, field) == whole
                assert evaluate(result['weighted_C'], z, field) == weighted
                assert evaluate(result['U'], z, field) == pow(gauss[1], m, field)
                assert evaluate(result['D'], z, field) == (1 if character == 0 else ell % field)
                for pair in result['pairs']:
                    expected = targets[pair['j']]*targets[pair['opposite']] % field
                    actual = evaluate(expand_pair_for_test(result, pair), z, field)
                    assert actual == expected
                    counts['direct_pair_checks'] += 1
                counts['character_components'] += 1
                counts['direct_whole_checks'] += 1
                counts['weighted_checks'] += 1
                d = m//gcd(character, m)
                if 1 < d < m:
                    counts['proper_divisor_components'] += 1
        counts['parameter_cases'] += 1
    for N, ell, m, expected in ((3*101,31,15,3), (5*101,31,15,5),
                                 (31*101,31,15,31), (3*5,31,15,3)):
        r = acquire(N, ell, m, repo_root)
        assert r['status'] == 'PUBLIC_FACTOR' and r['factor'] == expected
        counts['public_factor_checks'] += 1
    for N, ell, m in ((101*103,31,2), (101*103,31,9), (3,7,3)):
        try:
            acquire(N, ell, m, repo_root)
        except ValueError:
            counts['invalid_checks'] += 1
        else:
            raise AssertionError('invalid input accepted')
    # Optional cross-check of coordinated independent row-descriptor implementation.
    try:
        from composite_colours import canonical_rows
    except ImportError:
        counts['coordinated_rows'] = 'not available'
    else:
        for m, ell in ((3,7), (9,19), (15,31)):
            N = 101*103
            theirs = {r['j']: r for r in canonical_rows(N,m)}
            for r in rows(N,m):
                assert all(r[k] == theirs[r['j']][k] for k in ('a','b','ell','E'))
        counts['coordinated_rows'] = 'matched'
    return dict(status='PASS', counts=counts, max_packed_degree=degree,
                core_full_pair_expansion=False,
                scope='deterministic arithmetic/exception controls, not coverage or timing')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo-root', required=True)
    parser.add_argument('--json-out')
    args = parser.parse_args()
    result = run(args.repo_root)
    text = json.dumps(result, indent=2, sort_keys=True)
    print(text)
    if args.json_out:
        Path(args.json_out).write_text(text+'\n')
