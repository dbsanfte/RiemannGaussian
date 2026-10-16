#!/usr/bin/env python3
"""Optional public-input Fermat-quotient residue-catalog factoring probe.

Guarantee: N=P*Q, distinct odd primes, m an odd prime, N<=m**6,
and P,Q>16*m**2. If either factor's Fermat quotient modulo m belongs
to the supplied quotient set, factor_quotient_catalog returns a factor.
The optional include_equal flag also covers equal factor quotients using
the public identity q_m(P)+q_m(Q)=q_m(N). This covers specified input
classes, not all semiprimes. No factors,
orders, factor-indexed tables or external oracles enter the public API.
Uses the existing exact GMP-packed monic product/remainder-tree backend.
Self-tests are optional research replay, never ordinary CI.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import random
import runpy

import gmpy2


_BACKEND = runpy.run_path(str(Path(__file__).with_name(
    "probe_semiprime_long_period.py")))
MonicBatch = _BACKEND["MonicBatch"]


def _checked_factor(n, factor, **metadata):
    factor = int(factor)
    if not 1 < factor < n or n % factor:
        raise ArithmeticError("invalid factor returned by catalog descent")
    return {"status": "factor", "factor": factor, **metadata}


def _horner(poly, point, n):
    value = 0
    for coefficient in reversed(poly):
        value = (value * point + coefficient) % n
    return value


def factor_residue_catalog(n, step, residues, max_k):
    """Test all s+step*k, 0<=k<=max_k, by ONE monic multipoint batch.

    Residues are reduced modulo step and deduplicated. No-hit certifies
    only this exact finite grid. A saturated leaf can exist outside the
    caller's size promises; it returns unresolved-saturated, never a fake
    factor or a false no-hit. No root-by-point value array is constructed.
    """
    n, step, max_k = int(n), int(step), int(max_k)
    if n < 4 or step < 1 or max_k < 0:
        raise ValueError("n>=4, step>=1 and max_k>=0 are required")
    roots = sorted({int(s) % step for s in residues})
    batch = MonicBatch(n)
    details = {"catalog_size": len(roots), "point_count": max_k + 1,
               "step": step, "max_k": max_k, "saturated_rows": 0,
               "descent_nodes": 0}
    if not roots:
        return {"status": "no-hit", "factor": None,
                **details, **batch.stats()}
    root_tree = batch.tree(roots)
    points = [(-step * k) % n for k in range(max_k + 1)]
    values = batch.evaluate(root_tree[0], points)

    def descend(node, point):
        details["descent_nodes"] += 1
        if node[1] is None:
            return None  # this leaf is saturated, hence not a proper factor
        for child in node[1:]:
            divisor = math.gcd(_horner(child[0], point, n), n)
            if 1 < divisor < n:
                return divisor
            if divisor == n:
                found = descend(child, point)
                if found is not None:
                    return found
        return None

    for k, value in enumerate(values):
        divisor = math.gcd(int(value), n)
        if divisor == 1:
            continue
        if divisor == n:
            details["saturated_rows"] += 1
            divisor = descend(root_tree, points[k])
            if divisor is None:
                return {"status": "unresolved-saturated", "factor": None,
                        "row_k": k, **details, **batch.stats()}
        return _checked_factor(n, divisor, stage="residue-catalog", row_k=k,
                               **details, **batch.stats())
    return {"status": "no-hit", "factor": None,
            **details, **batch.stats()}


def _preflight(n, m):
    if n < 4:
        raise ValueError("n>=4 required")
    if m < 3 or m % 2 == 0 or not gmpy2.is_prime(m):
        raise ValueError("m must be an odd prime (public API premise)")
    if n % 2 == 0:
        return _checked_factor(n, 2, stage="even")
    divisor = math.gcd(n, m)
    if 1 < divisor < n:
        return _checked_factor(n, divisor, stage="modulus-gcd")
    square = math.isqrt(n)
    if square * square == n:
        return _checked_factor(n, square, stage="square")
    if divisor != 1:
        # n=m (or another out-of-contract input): reciprocal construction
        # modulo m^2 is not licensed; do not pretend this is a miss.
        return {"status": "outside-contract", "factor": None,
                "reason": "n is not coprime to m"}
    return None


def quotient_residues(n, m, quotients=(0,)):
    """Public catalog, containing both orientations of every supplied class.

    q_m(x)=((x^(m-1)-1)/m) mod m. Its tau-class is exactly
    {j^m*(1-m*tau) mod m^2: 1<=j<m}. Inversion below is modulo m^2,
    not modulo the unknown factors. Arbitrary/negative quotients normalize
    modulo m; duplicates are removed before any polynomial construction.
    """
    n, m = int(n), int(m)
    if m < 3 or m % 2 == 0 or not gmpy2.is_prime(m):
        raise ValueError("m must be an odd prime")
    if math.gcd(n, m) != 1:
        raise ValueError("catalog construction requires gcd(n,m)=1")
    taus = sorted({int(tau) % m for tau in quotients})
    d = m * m
    teich = [pow(j, m, d) for j in range(1, m)]
    direct = {r * (1 - m * tau) % d for tau in taus for r in teich}
    # Units modulo d have publicly computable inverses; this makes a
    # class on the larger factor capture the smaller factor's residue.
    catalog = direct | {(n * pow(r, -1, d)) % d for r in direct}
    return taus, sorted(direct), sorted(catalog)


def factor_quotient_catalog(n, m, quotients=(0,), include_equal=False):
    """Factor or certify a miss of the computed grid, with no private input.

    Under the module's semiprime/size/prefix promises, a no-hit return
    implies neither factor has Fermat quotient in the normalized supplied
    set. The converse need not hold: incidental grid multiples may factor
    other inputs too. No-hit is NOT a primality or general factoring test.
    With include_equal=True, also insert q_m(n)/2 modulo m, computed
    publicly. Additivity of the Fermat quotient then covers every promised
    input with equal factor quotients, including nonzero equal quotients.
    m's primality is a premise; gmpy2's probable-prime check merely rejects
    obvious invalid API inputs, not a new deterministic primality proof.
    Runtime is soft O((1+|quotients mod m|)*m), plus reading/reducing the
    explicit quotient metadata, including setup, for m at sixth-root scale.
    Arbitrarily expanded quotient sets retain that displayed cost.
    """
    n, m = int(n), int(m)
    early = _preflight(n, m)
    if early is not None:
        return early
    public_quotient = equal_quotient = None
    if include_equal:
        public_quotient = ((pow(n, m - 1, m * m) - 1) // m) % m
        equal_quotient = public_quotient * ((m + 1) // 2) % m
        quotients = tuple(quotients) + (equal_quotient,)
    taus, direct, catalog = quotient_residues(n, m, quotients)
    result = factor_residue_catalog(n, m * m, catalog, m)
    result.update(m=m, quotients=taus, direct_catalog_size=len(direct),
                  include_equal=bool(include_equal),
                  public_fermat_quotient=public_quotient,
                  equal_class_quotient=equal_quotient,
                  guarantee="conditional supplied Fermat-quotient class only",
                  premises="distinct odd semiprime; n<=m^6; both factors>16m^2")
    return result


def _fermat_quotient(x, m):
    # Reference-only helper; no factor is passed to the public algorithm.
    return ((pow(x, m - 1, m * m) - 1) // m) % m


def self_test():
    checks = 0
    rng = random.Random(20261016)
    for modulus in (35, 101 * 103, 1009 * 1013):
        roots = [rng.randrange(modulus) for _ in range(37)]
        points = [0, 0, modulus] + [rng.randrange(modulus) for _ in range(28)]
        batch = MonicBatch(modulus)
        polynomial = batch.tree(roots)[0]
        expected = [math.prod((x - r) % modulus for r in roots) % modulus
                    for x in points]
        assert batch.evaluate(polynomial, points) == expected
        assert batch.convolutions > 0
        checks += 1
    saturated = factor_residue_catalog(35, 100, [5, 7, 105, -93], 0)
    assert saturated["status"] == "factor" and saturated["saturated_rows"] == 1
    assert saturated["catalog_size"] == 2 and saturated["descent_nodes"] > 0
    checks += 1
    assert factor_residue_catalog(35, 100, [0], 0)["status"] == "unresolved-saturated"
    assert factor_residue_catalog(35, 100, [], 0)["status"] == "no-hit"
    checks += 2
    m = 23
    # Fixed valid sixth-scale fixture with equal NONZERO quotients. It is
    # missed by the default class but captured by the publicly derived one.
    equal_p, equal_q = 8467, 8867
    equal_n = equal_p * equal_q
    assert gmpy2.is_prime(equal_p) and gmpy2.is_prime(equal_q)
    assert equal_p != equal_q and min(equal_p,equal_q) > 16*m*m
    assert equal_n <= m**6
    assert _fermat_quotient(equal_p,m) == _fermat_quotient(equal_q,m) == 17
    assert factor_quotient_catalog(equal_n,m)["status"] == "no-hit"
    equal_hit = factor_quotient_catalog(equal_n,m,include_equal=True)
    assert equal_hit["status"] == "factor" and equal_n % equal_hit["factor"] == 0
    assert equal_hit["public_fermat_quotient"] == 11
    assert equal_hit["equal_class_quotient"] == 17
    assert equal_hit["quotients"] == [0,17] and equal_hit["include_equal"]
    checks += 1
    primes = [x for x in range(16 * m * m + 1, m ** 3)
              if gmpy2.is_prime(x)]
    p = next(x for x in primes if _fermat_quotient(x, m) != 0)
    # Larger-only exceptional factor: outside the entire direct candidate
    # range, but its reciprocal class captures the smaller p.
    q = next(x for x in range(m ** 3 + m * m + 1, m ** 6 // p + 1)
             if gmpy2.is_prime(x) and _fermat_quotient(x, m) == 0)
    n = p * q
    assert p > 16*m*m and q > 16*m*m and n <= m**6
    taus, direct, catalog = quotient_residues(n, m)
    assert p % (m*m) not in direct and p % (m*m) in catalog
    assert factor_residue_catalog(n, m*m, direct, m)["status"] == "no-hit"
    hit = factor_quotient_catalog(n, m)
    assert hit["status"] == "factor" and n % hit["factor"] == 0
    checks += 1
    q2 = next(x for x in primes if x != p and _fermat_quotient(x, m) != 0)
    n2 = p * q2
    tau = _fermat_quotient(p, m)
    nonzero = factor_quotient_catalog(n2, m, (tau, tau + m, tau - m))
    assert nonzero["status"] == "factor" and nonzero["quotients"] == [tau]
    checks += 1
    miss = factor_quotient_catalog(n2, m, ())
    assert miss["status"] == "no-hit"
    # Obtain a nonempty true miss and verify its full finite grid independently.
    for other_tau in range(m):
        candidate = factor_quotient_catalog(n2, m, (other_tau,))
        if candidate["status"] == "no-hit":
            _, _, residues = quotient_residues(n2, m, (other_tau,))
            assert all(math.gcd(s + m*m*k, n2) == 1
                       for s in residues for k in range(m + 1))
            assert other_tau not in (_fermat_quotient(p,m), _fermat_quotient(q2,m))
            break
    else:
        raise AssertionError("reference test did not find a nonempty miss")
    checks += 2
    assert factor_quotient_catalog(38, 23)["factor"] == 2
    assert factor_quotient_catalog(23*29, 23)["factor"] == 23
    assert factor_quotient_catalog(29**2, 23)["factor"] == 29
    for invalid in (0, 1, 2, 9):
        try:
            factor_quotient_catalog(35, invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid auxiliary prime accepted")
    checks += 7
    return {"self_test": "PASS", "test_groups": checks,
            "larger_factor_reciprocal_case": {"n": n, "m": m, "p": p, "q": q},
            "equal_nonzero_case": {"n": equal_n, "m": m,
                                   "factor_quotient": 17},
            "scope": "reference factors only in optional tests; not an all-input theorem"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int)
    parser.add_argument("--m", type=int)
    parser.add_argument("--quotients", default="0",
                        help="comma-separated integers; empty string gives empty catalog")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--include-equal", action="store_true",
                        help="also cover equal factor Fermat quotients via public q_m(n)/2")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(), indent=2))
        return
    if args.n is None or args.m is None:
        parser.error("--n and --m are required unless --self-test is supplied")
    taus = tuple(int(x.strip()) for x in args.quotients.split(",") if x.strip())
    print(json.dumps(factor_quotient_catalog(args.n, args.m, taus,
                                           include_equal=args.include_equal), indent=2))


if __name__ == "__main__":
    main()
