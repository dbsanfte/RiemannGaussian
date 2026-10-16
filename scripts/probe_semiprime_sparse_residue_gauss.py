#!/usr/bin/env python3
"""Optional exact sparse-residue/Gauss factoring probe (public inputs only).

Promised fast branch: N=P*Q, distinct odd primes, N<=w**6, w=Theta(N**(1/6)),
P,Q>16*w*w, alpha a unit with BOTH local orders odd and >16*w*w,
72<H, H**3<=N, and explicit unit residues S mod H contain min(P,Q) mod H.
No factors or orders enter factor_sparse_catalog. The return value always
checks a reported factor; no-hit is conditional on catalog coverage, not an
all-input factoring assertion. The alpha/order and scale promises are NOT
certified by this probe. Acquire alpha with the separately proved paid setup.

Exact 2D weighted Gauss replaces the rank-3 LLL rows. All residues share one
baby base, one compressed BSGS batch, and the existing GMP-packed MonicBatch.
For G=O(|S| log N), K=O(sqrt(N/H**3)), the catalog work is soft O(G+sqrt(G*K)).
Order screening costs soft sqrt(K). A saturated positive-order certificate
uses the explicit Burgess/dyadic annihilator extractor, with trial division
as finite-input fallback; its asymptotic bound is soft N**(31/192), given the
stated promises and a polylog-bit annihilator. The fallback is real code,
not an oracle, but can be slow outside the asymptotic promised regime.
Self-tests are optional research replay, not ordinary CI.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import runpy

import gmpy2


MonicBatch = runpy.run_path(str(Path(__file__).with_name(
    "probe_semiprime_long_period.py")))["MonicBatch"]


def _sorted_unique(values):
    """Deterministic sort/adjacent dedup, with no integer hash-table bound."""
    result = []
    for value in sorted(values):
        if not result or value != result[-1]:
            result.append(value)
    return result


def _quotient_residues(n, r, quotients):
    """Same public Teichmuller formula as the frozen quotient probe.

    Local deterministic sorting replaces its hash-based sets; the old
    implementation is neither imported nor modified.
    """
    taus = _sorted_unique(int(tau) % r for tau in quotients)
    modulus = r*r
    teich = [pow(j, r, modulus) for j in range(1, r)]
    direct = _sorted_unique(t*(1-r*tau) % modulus for tau in taus for t in teich)
    reciprocal = [(n*pow(t, -1, modulus)) % modulus for t in direct]
    return taus, direct, _sorted_unique(direct+reciprocal)


def _ceil_root(n, degree):
    root, exact = gmpy2.iroot(int(n), degree)
    return int(root) + (not exact)


def _nearest(num, den):
    """Exact nearest integer, with half-integer ties rounded down."""
    quo, rem = divmod(num, den)
    return quo + (2 * rem > den)


def _factor(n, divisor, **metadata):
    divisor = int(divisor)
    if not 1 < divisor < n or n % divisor:
        raise ArithmeticError("invalid proposed factor")
    return {"status": "factor", "factor": divisor, **metadata}


def _horner(poly, point, n):
    value = 0
    for coefficient in reversed(poly):
        value = (value * point + coefficient) % n
    return value


def weighted_gauss(n, h, residue, x):
    """Return/certify (a,b,c) with H²c-sHb+s²a=0 mod N, a!=0.

    Requires gcd(H,N)=gcd(s,H)=1, H>72, X>=1, HX<=2 floor(sqrt N).
    No hidden factor, floating-point norm, LLL, or approximate arithmetic.
    """
    n, h, residue, x = map(int, (n, h, residue, x))
    if (h <= 72 or x < 1 or h*x > 2*math.isqrt(n)
            or not 0 <= residue < h or math.gcd(residue, h) != 1
            or math.gcd(h, n) != 1):
        raise ValueError("weighted Gauss parameter promises failed")
    d = residue*residue + h*h*x*x
    weight = x*x*d
    kappa = residue*residue * pow(h, -1, n) % n
    first, second = (1, -kappa), (0, n)

    def dot(v, z):
        return weight*v[0]*z[0] + v[1]*z[1]

    iterations = 0
    while True:
        iterations += 1
        if dot(second, second) < dot(first, first):
            first, second = second, first
        norm = dot(first, first)
        inner = dot(first, second)
        if 2*abs(inner) <= norm:
            break
        multiple = _nearest(inner, norm)
        second = tuple(second[i]-multiple*first[i] for i in range(2))
    a, u = first
    f = dot(first, first)
    determinant = first[0]*second[1]-first[1]*second[0]
    if (abs(determinant) != n or f > dot(second, second)
            or 2*abs(dot(first, second)) > f
            or 3*f*f > 4*n*n*weight or a == 0
            or (u+kappa*a) % n):
        raise ArithmeticError("Gauss reduction certificate failed")
    divisor, lam, mu = map(int, gmpy2.gcdext(h, residue))
    if divisor != 1:
        raise ArithmeticError("nonprimitive lift")
    c0, b0 = lam*u, -mu*u
    shift = _nearest(-(residue*c0 + x*x*h*b0), d)
    c, b = c0+shift*residue, b0+shift*h
    norm3 = c*c+x*x*b*b+x**4*a*a
    if (h*c-residue*b != u
            or (h*h*c-residue*h*b+residue*residue*a) % n
            or 4*d*norm3 > 4*x*x*f+d*d):
        raise ArithmeticError("nearest-lift certificate failed")
    return {"a": a, "b": b, "c": c, "residue": residue, "X": x,
            "F": f, "D": d, "norm_squared": norm3,
            "iterations": iterations}


def first_power_collision(n, base, cap):
    """First positive e<=cap with gcd(base**e-1,N)>1, or exact no-hit.

    A proper gcd factors. A saturated FIRST leaf proves both local orders
    equal e (on semiprimes). Covers exact cap, with a separately truncated
    final block; no unlicensed padded exponents are inspected.
    """
    n, base, cap = int(n), int(base) % n, int(cap)
    if cap < 1 or math.gcd(base, n) != 1:
        raise ValueError("positive cap and unit base required")
    width = math.isqrt(cap-1)+1
    babies = [1]
    for _ in range(1, width):
        babies.append(babies[-1]*base % n)
    batch = MonicBatch(n)
    tree = batch.tree(babies)
    stride = pow(base, width, n)
    full, tail = divmod(cap, width)
    points, value = [], 1
    for _ in range(full):
        value = value*stride % n
        points.append(value)

    def inspect(node, point, offset):
        # Right first = larger baby index = smaller positive exponent.
        if node[1] is None:
            exponent = offset
            divisor = math.gcd((point+node[0][0]) % n, n)
            return divisor, exponent
        left, right = node[1], node[2]
        for child, child_offset in ((right, offset-(len(left[0])-1)),
                                    (left, offset)):
            if math.gcd(_horner(child[0], point, n), n) > 1:
                return inspect(child, point, child_offset)
        raise ArithmeticError("nonunit parent without nonunit child")

    values = batch.evaluate(tree[0], points)
    for block, (point, value) in enumerate(zip(points, values), 1):
        if math.gcd(value, n) > 1:
            divisor, exponent = inspect(tree, point, block*width)
            return {"status": "factor" if divisor < n else "common-order",
                    "factor": divisor if divisor < n else None,
                    "exponent": exponent, "cap": cap, **batch.stats()}
    if tail:
        start = width-tail
        tail_tree = batch.tree(babies[start:])
        point = pow(base, (full+1)*width, n)
        if math.gcd(_horner(tail_tree[0], point, n), n) > 1:
            divisor, exponent = inspect(tail_tree, point, (full+1)*width-start)
            return {"status": "factor" if divisor < n else "common-order",
                    "factor": divisor if divisor < n else None,
                    "exponent": exponent, "cap": cap, **batch.stats()}
    return {"status": "no-hit", "factor": None, "cap": cap, **batch.stats()}


def _trial_factor(n):
    if n % 2 == 0:
        return 2
    for candidate in range(3, math.isqrt(n)+1, 2):
        if n % candidate == 0:
            return candidate
    return None


def factor_annihilator(n, alpha, annihilator, scale):
    """Literal Burgess/dyadic extractor; K supplied, not acquired for free.

    Both odd local alpha orders >16*scale² and N<=scale**6 are the fast
    theorem's promises. Trial division supplies total finite-input fallback.
    """
    n, alpha, annihilator, scale = map(int, (n, alpha, annihilator, scale))
    if n < 5 or n % 2 == 0 or scale < 1:
        raise ValueError("odd N>=5 and positive scale required")
    stats = {"separator_calls": 0, "scanned_bases": 0,
             "trial_fallback": False, "annihilator_bits": abs(annihilator).bit_length()}
    divisor = math.gcd(alpha, n)
    if 1 < divisor < n:
        return _factor(n, divisor, stage="annihilator-base-gcd", **stats)
    if annihilator == 0 or divisor != 1 or pow(alpha, abs(annihilator), n) != 1:
        raise ValueError("a nonzero verified global annihilator is required")
    odd = abs(annihilator)
    while odd % 2 == 0:
        odd //= 2

    def scan_gcd(a):
        stats["scanned_bases"] += 1
        divisor = math.gcd(a, n)
        return divisor

    def fallback():
        stats["trial_fallback"] = True
        divisor = _trial_factor(n)
        if divisor is None:
            return {"status": "no-factor", "factor": None, **stats}
        return _factor(n, divisor, stage="annihilator-trial-fallback", **stats)

    jacobi_base = None
    for a in range(1, _ceil_root(n**5, 32)+1):
        divisor = scan_gcd(a)
        if 1 < divisor < n:
            return _factor(n, divisor, stage="annihilator-scan-gcd", **stats)
        if divisor == 1 and gmpy2.jacobi(a, n) == -1:
            jacobi_base = a
            break
    if jacobi_base is None:
        return fallback()
    b0 = pow(jacobi_base, odd, n)
    bound = 16*scale*scale
    x = 1
    while 2*x < bound:
        x *= 2
    while x <= math.isqrt(n):
        cap = (2*x+bound-1)//bound
        stats["separator_calls"] += 1
        result = first_power_collision(n, b0, cap)
        if result["status"] == "factor":
            return _factor(n, result["factor"], stage="annihilator-jacobi",
                           dyadic_X=x, **stats)
        if result["status"] == "common-order":
            y = (n+x-1)//x
            for a in range(1, _ceil_root(y**5, 32)+1):
                divisor = scan_gcd(a)
                if 1 < divisor < n:
                    return _factor(n, divisor, stage="annihilator-scan-gcd", **stats)
                if divisor != 1:
                    continue
                stats["separator_calls"] += 1
                result = first_power_collision(n, pow(a, odd, n), cap)
                if result["status"] == "factor":
                    return _factor(n, result["factor"], stage="annihilator-nonresidue",
                                   dyadic_X=x, **stats)
        x *= 2
    return fallback()


def _quadratic_factor(n, h, row, index):
    a, b, c, s = (row[key] for key in ("a", "b", "c", "residue"))
    middle = b*h-2*a*s-index*h*h
    constant = c*h*h-b*h*s+a*s*s
    discriminant = middle*middle-4*a*constant
    if discriminant < 0:
        return None
    root = math.isqrt(discriminant)
    if root*root != discriminant:
        return None
    for numerator in (-middle-root, -middle+root):
        if numerator % (2*a) == 0:
            candidate = numerator//(2*a)
            divisor = math.gcd(candidate, n)
            if 1 < divisor < n:
                return divisor
    return None


def _shared_collision(n, h, alpha, q, rows, cap, scale):
    """Compressed common-baby search; integer-trivial rows removed by caller."""
    count = cap+1
    width = min(count, math.isqrt(max(1, len(rows)*count)-1)+1)
    babies = [1]
    for _ in range(1, width):
        babies.append(babies[-1]*q % n)
    anchors = []
    inverse_stride = pow(pow(q, width, n), -1, n)
    for row_id, row in enumerate(rows):
        value = pow(alpha, row["E"], n)
        for offset in range(0, count, width):
            anchors.append((value, row_id, offset, min(width, count-offset)))
            value = value*inverse_stride % n
    info = {"giant_rows": len(rows), "baby_width": width,
            "compressed_anchors": len(anchors), "saturated_leaves": 0}
    batch = MonicBatch(n)
    for length in sorted({entry[3] for entry in anchors}):
        active = [entry for entry in anchors
                  if entry[3] == length]
        if not active:
            continue
        tree = batch.tree(babies[:length])
        values = batch.evaluate(tree[0], [entry[0] for entry in active])

        def descend(node, point, start):
            if node[1] is None:
                return math.gcd((point+node[0][0]) % n, n), start
            left, right = node[1], node[2]
            for child, first in ((left, start), (right, start+len(left[0])-1)):
                if math.gcd(_horner(child[0], point, n), n) > 1:
                    return descend(child, point, first)
            raise ArithmeticError("nonunit product with unit children")

        for entry, value in zip(active, values):
            divisor = math.gcd(value, n)
            if divisor == 1:
                continue
            point, row_id, offset, _ = entry
            if divisor == n:
                divisor, baby_index = descend(tree, point, 0)
                if divisor == n:
                    info["saturated_leaves"] += 1
                    index = offset+baby_index
                    annihilator = rows[row_id]["E"]-h*h*index
                    if annihilator == 0:
                        divisor = _quadratic_factor(n, h, rows[row_id], index)
                        if divisor is None:
                            raise ArithmeticError("unremoved trivial global match")
                    else:
                        result = factor_annihilator(n, alpha, annihilator, scale)
                        return {**result, "collision": info, "batch": batch.stats()}
            return _factor(n, divisor, stage="shared-monic-collision",
                           row_id=row_id, **info, **batch.stats())
    return {"status": "no-hit", "factor": None, **info, **batch.stats()}


def factor_sparse_catalog(n, h, residues, alpha, *, scale):
    """Factor under the module's explicit coverage/order/scale promises.

    A no-hit result certifies the searched rows only. It implies failure
    of the residue-coverage promise only when all OTHER promises hold.
    """
    n, h, alpha, scale = map(int, (n, h, alpha, scale))
    if n < 4 or scale < 1 or n > scale**6 or h <= 72 or h**3 > n:
        raise ValueError("require N>=4,N<=scale**6,72<H,H**3<=N")
    if n % 2 == 0:
        return _factor(n, 2, stage="even")
    square = math.isqrt(n)
    if square*square == n:
        return _factor(n, square, stage="square")
    for value, name in ((h, "modulus"), (alpha, "alpha")):
        divisor = math.gcd(value, n)
        if 1 < divisor < n:
            return _factor(n, divisor, stage=name+"-gcd")
        if divisor != 1:
            raise ValueError(name+" must be a unit modulo N")
    normalized = _sorted_unique(int(s) % h for s in residues)
    if any(math.gcd(s, h) != 1 for s in normalized):
        raise ValueError("catalog residues must be units modulo H")
    quotient = (n+h**3-1)//h**3
    cap = 8*(math.isqrt(quotient-1)+1)
    metadata = {"N": n, "H": h, "scale": scale,
                "catalog_size": len(normalized), "seed_cap": cap,
                "order_promises_checked": False,
                "guarantee": "conditional explicit smaller-factor residue coverage"}
    if not normalized:
        return {"status": "no-hit", "factor": None, **metadata}
    alpha %= n
    q = pow(alpha, h*h, n)
    screen = first_power_collision(n, q, cap)
    if screen["status"] == "factor":
        return _factor(n, screen["factor"], stage="unit-prefix-screen",
                       prefix_screen=screen, **metadata)
    if screen["status"] == "common-order":
        result = factor_annihilator(n, alpha, h*h*screen["exponent"], scale)
        return {**result, "prefix_screen": screen, **metadata}
    rows = []
    trivial = 0
    for residue in normalized:
        x = 1
        while h*x <= 2*math.isqrt(n):
            certificate = weighted_gauss(n, h, residue, x)
            for sign in (1, -1):
                row = {**certificate,
                       **{key: sign*certificate[key] for key in ("a", "b", "c")}}
                row["E"] = (row["c"]*h*h+row["b"]*h*(1-residue)
                            +row["a"]*(1-residue)**2)
                if row["E"] % (h*h) == 0 and 0 <= row["E"]//(h*h) <= cap:
                    index = row["E"]//(h*h)
                    divisor = _quadratic_factor(n, h, row, index)
                    if divisor is not None:
                        return _factor(n, divisor, stage="integer-trivial-quadratic",
                                       prefix_screen=screen, **metadata)
                    trivial += 1
                    continue
                rows.append(row)
            x *= 2
    result = _shared_collision(n, h, alpha, q, rows, cap, scale)
    return {**result, "integer_trivial_rows": trivial,
            "prefix_screen": screen, **metadata}


def factor_quotient_gauss(n, auxiliary_prime, alpha, *, scale,
                          quotients=(0,), include_equal=False, multiplier=None):
    """Construct the public quotient catalog, CRT-lift it, then share ONE batch.

    Either factor's q_r value in A (or equal factor q_r values when requested)
    ensures smaller-factor coverage. The auxiliary odd prime r need NOT be
    the sixth-root scale. Primality is a premise; the probable-prime rejection
    used for rejection is not a deterministic primality proof.
    Explicit catalog construction and all phi(M) CRT lifts are charged.
    Automatic M is near (N/(J²*r⁶))**(1/5), with finite admissibility clamps.
    Outside the finite H regime returns outside-contract, not false no-hit.
    """
    n, r, alpha, scale = map(int, (n, auxiliary_prime, alpha, scale))
    if n < 4 or r < 3 or r % 2 == 0 or not gmpy2.is_prime(r):
        raise ValueError("N>=4 and an odd auxiliary prime required")
    if n % 2 == 0:
        return _factor(n, 2, stage="even")
    divisor = math.gcd(n, r)
    if 1 < divisor < n:
        return _factor(n, divisor, stage="auxiliary-prime-gcd")
    if divisor != 1:
        return {"status": "outside-contract", "factor": None,
                "reason": "auxiliary prime not coprime to N"}
    public_quotient = equal_class = None
    if include_equal:
        public_quotient = ((pow(n, r-1, r*r)-1)//r) % r
        equal_class = public_quotient*((r+1)//2) % r
        quotients = tuple(quotients)+(equal_class,)
    taus, direct, catalog = _quotient_residues(n, r, quotients)
    info = {"auxiliary_prime": r, "quotients": taus,
            "include_equal": bool(include_equal),
            "public_fermat_quotient": public_quotient,
            "equal_class_quotient": equal_class,
            "direct_catalog_size": len(direct), "base_catalog_size": len(catalog)}
    if not catalog:
        return {"status": "no-hit", "factor": None, **info}
    residue_modulus = r*r
    max_multiplier = int(gmpy2.iroot(n, 3)[0])//residue_modulus
    if multiplier is None:
        estimate = n//(len(catalog)**2*r**6)
        multiplier = max(1, int(gmpy2.iroot(estimate, 5)[0]),
                         72//residue_modulus+1)
        while math.gcd(multiplier, r) != 1:
            multiplier += 1
    multiplier = int(multiplier)
    if (multiplier < 1 or multiplier > max_multiplier
            or math.gcd(multiplier, r) != 1 or multiplier*residue_modulus <= 72):
        return {"status": "outside-contract", "factor": None,
                "reason": "no admissible chosen 72<H=M*r² with H³<=N",
                "multiplier": multiplier, **info}
    divisor = math.gcd(multiplier, n)
    if 1 < divisor < n:
        return _factor(n, divisor, stage="CRT-multiplier-gcd", **info)
    if divisor != 1:
        return {"status": "outside-contract", "factor": None,
                "reason": "CRT multiplier not a unit modulo N", **info}
    units = [j for j in range(multiplier) if math.gcd(j, multiplier) == 1]
    # gcd(0,1)=1: the M=1 branch has one CRT lift, as it should.
    inverse = pow(residue_modulus, -1, multiplier) if multiplier > 1 else 0
    h = multiplier*residue_modulus
    lifted = []
    for s in catalog:
        for j in units:
            z = s+residue_modulus*((j-s)*inverse % multiplier)
            # Paired construction certifies the original residue directly;
            # no O(J) catalog-membership scan is hidden in each CRT lift.
            if z % residue_modulus != s or math.gcd(z, h) != 1:
                raise ArithmeticError("CRT lift certificate failed")
            lifted.append(z)
    result = factor_sparse_catalog(n, h, lifted, alpha, scale=scale)
    return {**result, **info, "multiplier": multiplier,
            "CRT_unit_count": len(units), "lifted_catalog_size": len(lifted)}


def _self_test():
    """Small exact checks; production functions never receive reference factors."""
    checks = 0
    batch = MonicBatch(101*103)
    roots = [(i*i+3*i+7) % (101*103) for i in range(37)]
    points = [0, 0]+[(i**3+19) % (101*103) for i in range(29)]
    polynomial = batch.tree(roots)[0]
    assert batch.evaluate(polynomial, points) == [
        math.prod((point-root) % (101*103) for root in roots) % (101*103)
        for point in points]
    assert batch.convolutions > 0
    checks += 1
    for n in (35, 77, 143):
        for base in range(1, min(n, 12)):
            if math.gcd(base, n) != 1:
                continue
            for cap in (1, 2, 3, 5, 8, 10, 17):
                expected = next((i for i in range(1, cap+1)
                                 if math.gcd(pow(base, i, n)-1, n) > 1), None)
                result = first_power_collision(n, base, cap)
                assert (result["status"] == "no-hit") == (expected is None)
                if expected is not None:
                    assert result["exponent"] == expected
                    divisor = math.gcd(pow(base, expected, n)-1, n)
                    assert result["status"] == ("common-order" if divisor == n else "factor")
                checks += 1
    # Safe primes with (p-1)/2,(q-1)/2>16*43², N<=43⁶.
    p, q, w, alpha = 59447, 59747, 43, 4
    assert gmpy2.is_prime(p) and gmpy2.is_prime(q)
    assert gmpy2.is_prime((p-1)//2) and gmpy2.is_prime((q-1)//2)
    assert min((p-1)//2, (q-1)//2) > 16*w*w
    n = p*q
    assert n <= w**6
    assert 2*503 > _ceil_root(n, 4)  # outside GFHP's quoted H<N**(1/4)/2
    for h in (73, 127, 503):
        if h**3 > n:
            continue
        # 503>N**(1/4)/2 exercises the new Gauss domain.
        for residue in (p % h, q % h, 1):
            if math.gcd(residue, h) != 1:
                continue
            x = 1
            while h*x <= 2*math.isqrt(n):
                row = weighted_gauss(n, h, residue, x)
                assert row["a"] != 0
                assert (h*h*row["c"]-residue*h*row["b"]
                        +residue**2*row["a"]) % n == 0
                if residue == p % h:
                    own = (p-residue)//h
                    if x//2 <= own <= x:
                        value = row["c"]+row["b"]*own+row["a"]*own*own
                        assert value % p == 0
                        cap = 8*_ceil_root((n+h**3-1)//h**3, 2)
                        assert abs(value//p) <= cap
                checks += 1
                x *= 2
        result = factor_sparse_catalog(n, h, [p % h, 1, p % h], alpha, scale=w)
        assert result["status"] == "factor" and n % result["factor"] == 0
        assert result["prefix_screen"]["status"] == "no-hit"
        assert result["compressed_anchors"] > 0
        checks += 1
    miss = factor_sparse_catalog(n, 503, [1], alpha, scale=w)
    assert miss["status"] == "no-hit" and miss["integer_trivial_rows"] > 0
    assert factor_sparse_catalog(n, 503, [], alpha, scale=w)["status"] == "no-hit"
    checks += 2
    # Direct extractor replay, with independently known test-only order multiple.
    order_multiple = math.lcm((p-1)//2, (q-1)//2)
    result = factor_annihilator(n, alpha, order_multiple, w)
    assert result["status"] == "factor" and n % result["factor"] == 0
    checks += 1
    # Public equal-quotient class at a MUCH smaller auxiliary prime.
    assert ((pow(p, 4, 25)-1)//5) % 5 == ((pow(q, 4, 25)-1)//5) % 5 == 1
    wrapped = factor_quotient_gauss(n, 5, alpha, scale=w, include_equal=True)
    assert wrapped["status"] == "factor" and n % wrapped["factor"] == 0
    assert wrapped["equal_class_quotient"] == 1
    assert wrapped["lifted_catalog_size"] == (wrapped["base_catalog_size"]
                                                * wrapped["CRT_unit_count"])
    checks += 1
    # Both local alpha orders exactly H²=56169: positive saturated screen
    # supplies a nonzero annihilator; actual dyadic recovery, not an oracle.
    sat_n, sat_h, sat_alpha, sat_w = 25239989503, 237, 16, 55
    sat_p, sat_q, order = 112339, 224677, 56169
    assert sat_p*sat_q == sat_n and gmpy2.is_prime(sat_p) and gmpy2.is_prime(sat_q)
    assert order > 16*sat_w*sat_w and sat_n <= sat_w**6
    for prime in (sat_p, sat_q):
        assert pow(sat_alpha, order, prime) == 1
        assert all(pow(sat_alpha, order//ell, prime) != 1 for ell in (3, 79))
    saturated = factor_sparse_catalog(sat_n, sat_h, [1], sat_alpha, scale=sat_w)
    assert saturated["status"] == "factor"
    assert saturated["prefix_screen"]["exponent"] == 1
    assert not saturated["trial_fallback"]
    checks += 1
    # Actual certified Gauss row, nonzero negative global K at a compressed
    # baby/giant leaf, independently of the positive-order preflight case.
    row = weighted_gauss(sat_n, 73, 10, 1)
    row.update({key: -row[key] for key in ("a", "b", "c")})
    row["E"] = row["c"]*73**2+row["b"]*73*(1-10)+row["a"]*(1-10)**2
    assert row["E"] == 657 and row["E"]-73**2*1539 == -8200674
    cap = 8*_ceil_root((sat_n+73**3-1)//73**3, 2)
    common_q = pow(sat_alpha, 73**2, sat_n)
    assert first_power_collision(sat_n, common_q, cap)["status"] == "no-hit"
    global_leaf = _shared_collision(sat_n, 73, sat_alpha, common_q,
                                    [row], cap, sat_w)
    assert global_leaf["status"] == "factor"
    assert global_leaf["collision"]["saturated_leaves"] == 1
    assert not global_leaf["trial_fallback"]
    checks += 1
    fallback = factor_annihilator(35, 1, 1, 10)  # intentionally outside order promise
    assert fallback["status"] == "factor" and fallback["trial_fallback"]
    checks += 1
    return {"status": "pass", "checks": checks}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--n", type=int)
    parser.add_argument("--h", type=int)
    parser.add_argument("--residues", default="")
    parser.add_argument("--alpha", type=int)
    parser.add_argument("--scale", type=int)
    parser.add_argument("--aux-prime", type=int)
    parser.add_argument("--quotients", default="0")
    parser.add_argument("--include-equal", action="store_true")
    parser.add_argument("--multiplier", type=int)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        result = _self_test()
    else:
        if args.n is None or args.scale is None or args.alpha is None:
            parser.error("--n, --scale and explicit --alpha are required")
        if args.aux_prime is not None:
            quotients = [int(piece) for piece in args.quotients.split(",") if piece.strip()]
            result = factor_quotient_gauss(args.n, args.aux_prime, args.alpha,
                                           scale=args.scale, quotients=quotients,
                                           include_equal=args.include_equal,
                                           multiplier=args.multiplier)
        else:
            if args.h is None:
                parser.error("--h required for direct sparse-catalog mode")
            residues = [int(piece) for piece in args.residues.split(",") if piece.strip()]
            result = factor_sparse_catalog(args.n, args.h, residues, args.alpha,
                                           scale=args.scale)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
