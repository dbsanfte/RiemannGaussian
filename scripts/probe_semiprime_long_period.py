#!/usr/bin/env python3
"""Cheap transformed-period extraction; optional semiprime research replay.

Public-input algorithms only. Dickson aliases extend a cover but need not
hit every long order. The curve pass is classical ECM with a charged fast
polynomial continuation, not a new deterministic one-sixth theorem.
Reference factors occur only in validation/sample generation.
No persistent or factor-indexed precomputation. Never run in ordinary CI.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import statistics
import time

import gmpy2

ROOT = Path(__file__).resolve().parents[1]
QUADRATIC = runpy.run_path(str(ROOT / "scripts/probe_semiprime_quadratic_extraction.py"))
SINGLE = QUADRATIC["SINGLE"]
WEIGHTED = SINGLE["WEIGHTED"]


class MonicBatch:
    """General multipoint evaluation over Z/NZ; no field assumption.

    Monic divisors make Newton reciprocals legal even for composite N.
    This is the usual product/remainder tree, using our exact GMP packing.
    Counts measure actual convolutions, not an inferred runtime exponent.
    """

    def __init__(self, n):
        self.n = n
        self.convolutions = 0
        self.packed_coefficients = 0
        self.reductions = 0

    def mul(self, a, b):
        if not a or not b:
            return []
        self.convolutions += 1
        self.packed_coefficients += len(a) + len(b)
        if min(len(a), len(b)) <= 8:
            out = [0] * (len(a) + len(b) - 1)
            for i, x in enumerate(a):
                for j, y in enumerate(b):
                    out[i+j] = (out[i+j] + x*y) % self.n
            return out
        return WEIGHTED["mul"](a, b, self.n)

    def trim(self, a):
        a = list(a)
        while a and a[-1] == 0:
            a.pop()
        return a

    def reciprocal(self, f, length):
        assert f and f[0] == 1
        g = [1]
        while len(g) < length:
            target = min(2*len(g), length)
            fg = self.mul(f[:target], g)[:target]
            fg += [0] * (target-len(fg))
            correction = [(-v) % self.n for v in fg]
            correction[0] = (correction[0] + 2) % self.n
            g = self.mul(g, correction)[:target]
        return g

    def mod(self, f, g):
        assert g and g[-1] == 1
        self.reductions += 1
        f = self.trim(f)
        if len(f) < len(g):
            return f
        if len(g) <= 17:
            out = f[:]
            for i in range(len(out)-1, len(g)-2, -1):
                coefficient = out[i]
                start = i-len(g)+1
                for j, v in enumerate(g):
                    out[start+j] = (out[start+j]-coefficient*v) % self.n
            return self.trim(out[:len(g)-1])
        length = len(f)-len(g)+1
        inverse = self.reciprocal(g[::-1], length)
        qr = self.mul(f[::-1][:length], inverse)[:length]
        q = qr[::-1]
        product = self.mul(q, g)
        remainder = [(f[i]-product[i]) % self.n for i in range(len(g)-1)]
        return self.trim(remainder)

    def tree(self, values):
        if not values:
            return ([1], None, None)
        nodes = [([(-v) % self.n, 1], None, None) for v in values]
        while len(nodes) > 1:
            nxt = []
            for i in range(0, len(nodes), 2):
                if i+1 == len(nodes):
                    nxt.append(nodes[i])
                else:
                    a, b = nodes[i:i+2]
                    nxt.append((self.mul(a[0], b[0]), a, b))
            nodes = nxt
        return nodes[0]

    def evaluate(self, f, points):
        if not points:
            return []
        target_tree = self.tree(points)
        out = []

        def visit(node, remainder):
            remainder = self.mod(remainder, node[0])
            if node[1] is None:
                out.append(remainder[0] if remainder else 0)
            else:
                visit(node[1], remainder)
                visit(node[2], remainder)

        visit(target_tree, f)
        return out

    def stats(self):
        return {"convolutions": self.convolutions,
                "packed_coefficients": self.packed_coefficients,
                "monic_reductions": self.reductions}


def collision_from_tree(n, batch, node, roots, points):
    """Reuse the baby product when inspecting successive target batches."""
    values = batch.evaluate(node[0], points)
    for j, value in enumerate(values):
        g = math.gcd(value, n)
        if g != 1:
            if g == n:
                g = WEIGHTED["descend"](node, points[j], n)
            if g and 1 < g < n:
                # Recovery witness is located only after a successful GCD.
                for i, root in enumerate(roots):
                    if (points[j]-root) % g == 0:
                        return {"status": "factor", "factor": g,
                                "baby_index": i, "giant_index": j,
                                "root": root, "point": points[j], **batch.stats()}
            return {"status": "shared-collision", "factor": None, **batch.stats()}
    return {"status": "no-collision", "factor": None, **batch.stats()}


def collision_batch(n, roots, points):
    """First nonunit product, including exact descent of a shared collision."""
    batch = MonicBatch(n)
    return collision_from_tree(n, batch, batch.tree(roots), roots, points)


def dickson_integer(x, degree, parameter=1):
    """Exact D_degree(x,parameter); fixed degree costs polynomial in log x."""
    a, b = 2, x
    for _ in range(1, degree):
        a, b = b, x*b-parameter*a
    return a if degree == 0 else b


def difference_table(function, degree, start=0):
    row = [function(start+i) for i in range(degree+1)]
    out = []
    while row:
        out.append(row[0])
        row = [y-x for x, y in zip(row, row[1:])]
    return out


def quadratic_polynomial_powers(ring, alpha, function, degree, count, start=0):
    """alpha**f(i) via multiplicative finite differences, no giant exponents
    per point. All table construction/exponentiation is charged to the call.
    """
    differences = difference_table(function, degree, start)
    inverse = ring.inverse_one(alpha)
    state = [ring.power(alpha if e >= 0 else inverse, abs(e)) for e in differences]
    out = []
    for _ in range(count):
        out.append(state[0])
        # Ascending update uses the still-old next difference.
        for i in range(degree):
            state[i] = ring.mul(state[i], state[i+1])
    return out


def factor_dickson(n, degree=6, parameter=1, discriminant=-1,
                   order_divisor=1):
    """N-1/Jacobi separator + trace folding + nonlinear order aliases.

    Receives no private order. Success can occur above B^2; failure certifies
    only that this particular nonlinear cover has no separating collision.
    """
    if n < 4 or degree < 1 or order_divisor < 1:
        raise ValueError("composite n>=4 and positive degree/budget required")
    if n % 2 == 0:
        return {"status": "factor", "factor": 2, "stage": "even"}
    root = math.isqrt(n)
    if root*root == n:
        return {"status": "factor", "factor": root, "stage": "square"}
    d = discriminant
    g = math.gcd(d, n)
    if g != 1:
        return {"status": "factor" if 1 < g < n else "nonunit-colour",
                "factor": g if 1 < g < n else None, "stage": "colour"}
    colour = int(gmpy2.jacobi(d, n))
    ring = QUADRATIC["QuadraticRing"](n, d)
    for a in range(1, 33):
        den = (a*a-d) % n
        g = math.gcd(den, n)
        if 1 < g < n:
            return {"status": "factor", "factor": g, "stage": "parameter"}
        if g != 1:
            continue
        inv = pow(den, -1, n)
        unit = ((a*a+d)*inv % n, 2*a*inv % n)
        alpha = ring.power(unit, n-colour)
        if alpha != (1, 0):
            break
    else:
        return {"status": "kernel-unresolved", "factor": None}
    bound = SINGLE["ceil_root"](n, 6)
    info = {"bound": bound, "degree": degree, "parameter": parameter,
            "discriminant": d, "jacobi": colour, "base_parameter": a}
    powers = SINGLE["projection_powers"](bound, root+1)
    for _, e in [(0, 1)] + powers:
        alpha = ring.power(alpha, e)
        g = math.gcd(alpha[0]-1, n)
        if 1 < g < n:
            return {**info, "status": "factor", "factor": g, "stage": "projection"}
        if g == n:
            return {**info, "status": "shared-projection", "factor": None}
    limit = max(1, bound*bound//order_divisor)
    width = SINGLE["ceil_root"](limit, 2)
    blocks = (limit+width-1)//width
    f = lambda x: dickson_integer(x, degree, parameter)
    baby = quadratic_polynomial_powers(ring, alpha, f, degree, width)
    giant = quadratic_polynomial_powers(ring, alpha, lambda j: f(width*j),
                                         degree, blocks, start=1)
    # Norm-one conjugation folds BOTH signs: trace(u)=trace(v) iff u=v or v^-1.
    roots = [2*v[0] % n for v in baby]
    points = [2*v[0] % n for v in giant]
    result = collision_batch(n, roots, points)
    result.update(info)
    result.update({"stage": "dickson-cover", "projected_base": list(alpha),
                   "linear_cover": width*blocks, "baby_count": width,
                   "giant_count": blocks, "finite_difference_updates": degree*(width+blocks),
                   "projection_count": len(powers)})
    if result["factor"]:
        i, j = result["baby_index"], result["giant_index"]+1
        result["collision_exponents"] = [str(f(i)), str(f(width*j))]
    return result


def montgomery_double(point, a24, n):
    x, z = point
    a = (x+z)**2 % n
    b = (x-z)**2 % n
    c = (a-b) % n
    return a*b % n, c*(b+a24*c) % n


def montgomery_add(left, right, difference, n):
    x, z = left
    y, w = right
    dx, dz = difference
    a, b = (x+z)*(y-w) % n, (x-z)*(y+w) % n
    return dz*(a+b)**2 % n, dx*(a-b)**2 % n


def montgomery_scale(point, k, a24, n):
    if k == 0:
        return (1, 0)
    left, right = point, montgomery_double(point, a24, n)
    for bit in bin(k)[3:]:
        if bit == "0":
            left, right = (montgomery_double(left, a24, n),
                           montgomery_add(left, right, point, n))
        else:
            left, right = (montgomery_add(left, right, point, n),
                           montgomery_double(right, a24, n))
    return left


def point_progression(point, count, a24, n):
    out = []
    previous, current = (1, 0), point
    for i in range(count):
        out.append(current)
        if i == 0:
            following = montgomery_double(point, a24, n)
        else:
            following = montgomery_add(current, point, previous, n)
        previous, current = current, following
    return out


def invert_coordinates(n, points):
    """One inversion plus charged prefixes; nonunits supply factors first."""
    prefix = [1]
    for _, z in points:
        g = math.gcd(z, n)
        if g != 1:
            return None, g
        prefix.append(prefix[-1]*z % n)
    inv = pow(prefix[-1], -1, n)
    out = [0] * len(points)
    for i in range(len(points)-1, -1, -1):
        out[i] = points[i][0]*inv*prefix[i] % n
        inv = inv*points[i][1] % n
    return out, 1


def curve_extract(n, max_curves=12, order_divisor=1, staged=True):
    """Classical Suyama ECM; each curve has soft-O(N^(1/6)) bounded work.

    Fixed curve count has no guaranteed hit rate. No reference factors,
    curve orders, exhaustive B^2 prime list or hidden factoring API.
    """
    if n < 4 or max_curves < 1 or order_divisor < 1:
        raise ValueError("composite n>=4 and positive limits required")
    if n % 2 == 0:
        return {"status": "factor", "factor": 2, "stage": "even"}
    pmax = math.isqrt(n)
    if pmax*pmax == n:
        return {"status": "factor", "factor": pmax, "stage": "square"}
    bound = SINGLE["ceil_root"](n, 6)
    # Integer upper bound for the smaller prime's Hasse interval.
    group_bound = pmax + 2*math.isqrt(pmax) + 3
    powers = SINGLE["projection_powers"](bound, group_bound)
    limit = max(1, bound*bound//order_divisor)
    width = max(2, SINGLE["ceil_root"](limit, 2))
    blocks = (limit+width-1)//width
    history = []
    for curve_index in range(max_curves):
        sigma = curve_index+6
        info = {"bound": bound, "sigma": sigma, "curves_used": curve_index+1,
                "projection_count": len(powers), "linear_cover": width*blocks}
        u, v = (sigma*sigma-5) % n, 4*sigma % n
        x, z = pow(u, 3, n), pow(v, 3, n)
        denominator = 16*x*v % n
        g = math.gcd(denominator, n)
        if 1 < g < n:
            return {**info, "status": "factor", "factor": g, "stage": "curve-setup"}
        if g != 1:
            history.append({"sigma": sigma, "status": "shared-setup"})
            continue
        a24 = pow(v-u, 3, n)*(3*u+v)*pow(denominator, -1, n) % n
        g = math.gcd(a24*(a24-1), n)
        if 1 < g < n:
            return {**info, "status": "factor", "factor": g, "stage": "singular-curve"}
        if g != 1:
            history.append({"sigma": sigma, "status": "shared-singular"})
            continue
        point = (x, z)
        for _, e in powers:
            point = montgomery_scale(point, e, a24, n)
            g = math.gcd(point[1], n)
            if g != 1:
                break
        if 1 < g < n:
            return {**info, "status": "factor", "factor": g, "stage": "curve-smooth"}
        if g != 1:
            history.append({"sigma": sigma, "status": "shared-smooth"})
            continue
        # Disjoint integer indices are essential: including width on both
        # sides would give the meaningless collision width==width mod N.
        baby_points = point_progression(point, width-1, a24, n)
        step = montgomery_scale(point, width, a24, n)
        coordinates, g = invert_coordinates(n, baby_points)
        if 1 < g < n:
            return {**info, "status": "factor", "factor": g, "stage": "curve-coordinate"}
        if g != 1:
            history.append({"sigma": sigma, "status": "shared-coordinate"})
            continue
        roots = coordinates
        batch = MonicBatch(n)
        node = batch.tree(roots)
        previous, current = (1, 0), step
        visited, batch_size, target_batches = 0, 1 if staged else blocks, 0
        result = {"factor": None, "status": "no-collision"}
        while visited < blocks:
            count = min(batch_size, blocks-visited)
            target = []
            for j in range(count):
                target.append(current)
                if visited+j == 0:
                    following = montgomery_double(step, a24, n)
                else:
                    following = montgomery_add(current, step, previous, n)
                previous, current = current, following
            points, g = invert_coordinates(n, target)
            if 1 < g < n:
                return {**info, "status": "factor", "factor": g,
                        "stage": "curve-coordinate", "giant_count": visited+count}
            if g != 1:
                result = {"status": "shared-coordinate", "factor": None}
                break
            target_batches += 1
            result = collision_from_tree(n, batch, node, roots, points)
            if result["factor"]:
                result["giant_index"] += visited
            visited += count
            if result["status"] != "no-collision":
                break
            # Doubling batches gives O(log B) reductions of a degree-B
            # polynomial, retaining soft-linear worst-case work. Fixed-size
            # repeated batches would accidentally restore quadratic cost.
            batch_size *= 2
        if result["factor"]:
            result.update(info)
            result.update({"stage": "curve-cover", "baby_count": width-1,
                           "giant_count": visited, "projected_point": list(point),
                           "a24": a24, "earlier_curves": history,
                           "target_batches": target_batches, "staged": staged})
            # Equal x means equal/opposite points; verify either multiple
            # after recovery, without knowing the local order in advance.
            i, j = result["baby_index"]+1, result["giant_index"]+1
            f = result["factor"]
            annihilators = [j*width-i, j*width+i]
            result["verified_local_annihilators"] = [
                e for e in annihilators
                if montgomery_scale(point, e, a24, f)[1] % f == 0]
            assert result["verified_local_annihilators"]
            return result
        history.append({"sigma": sigma, "status": result["status"]})
    return {"status": "curve-budget-exhausted", "factor": None, "bound": bound,
            "curves_used": max_curves, "history": history}


def safe_json(value):
    if isinstance(value, int) and abs(value) > 2**53:
        return str(value)
    if isinstance(value, dict):
        return {k: safe_json(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [safe_json(v) for v in value]
    return value


def source_hashes():
    files = [Path(__file__), ROOT / "scripts/probe_semiprime_weighted_batch.py",
             ROOT / "scripts/probe_semiprime_single_extraction.py",
             ROOT / "scripts/probe_semiprime_quadratic_extraction.py"]
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def validate():
    rng = random.Random(2026100663)
    checks = {"monic_remainders": 0, "multipoint": 0,
              "finite_differences": 0, "trace_folding": 0, "curve_points": 0}
    for n in (15, 35, 77, 101*103, 1009*1013):
        batch = MonicBatch(n)
        for degree in (1, 3, 8, 16, 17, 31, 65):
            g = [rng.randrange(n) for _ in range(degree)]+[1]
            for extra in (0, 1, 5, degree, degree+7):
                f = [rng.randrange(n) for _ in range(degree+extra+1)]
                r = batch.mod(f, g)
                for x in (0, 1, 2, n-1):
                    assert (WEIGHTED["horner"](f, x, n)-WEIGHTED["horner"](r, x, n)) % math.gcd(WEIGHTED["horner"](g, x, n), n) == 0
                # Independent elementary long division, not just point tests.
                oracle = f[:]
                for i in range(len(oracle)-1, degree-1, -1):
                    c = oracle[i]
                    for j, v in enumerate(g):
                        oracle[i-degree+j] = (oracle[i-degree+j]-c*v) % n
                assert r == batch.trim(oracle[:degree])
                checks["monic_remainders"] += 1
        for count in (1, 2, 7, 18, 33, 64):
            points = [rng.randrange(n) for _ in range(count)]
            f = [rng.randrange(n) for _ in range(2*count+1)]
            assert batch.evaluate(f, points) == [WEIGHTED["horner"](f, x, n) for x in points]
            checks["multipoint"] += count
        ring = QUADRATIC["QuadraticRing"](n, -1)
        for a in range(1, 8):
            den = (a*a+1) % n
            if math.gcd(den, n) != 1:
                continue
            inv = pow(den, -1, n)
            alpha = ((a*a-1)*inv % n, 2*a*inv % n)
            for degree in (1, 2, 4, 6, 12):
                f = lambda x: dickson_integer(x, degree, 1)
                fast = quadratic_polynomial_powers(ring, alpha, f, degree, 23)
                for i, value in enumerate(fast):
                    e = f(i)
                    expected = ring.power(alpha if e >= 0 else ring.inverse_one(alpha), abs(e))
                    assert value == expected
                    checks["finite_differences"] += 1
            if gmpy2.is_prime(n):
                continue
            for prime in (p for p in (3, 5, 7, 11, 101, 103, 1009, 1013) if n % p == 0):
                for i in range(1, 12):
                    left, right = ring.power(alpha, i), ring.power(alpha, 12-i)
                    trace_equal = (left[0]-right[0]) % prime == 0
                    equal = all((x-y) % prime == 0 for x, y in zip(left, right))
                    inverse_equal = all((x-y) % prime == 0 for x, y in zip(left, ring.inverse_one(right)))
                    assert trace_equal == (equal or inverse_equal)
                    checks["trace_folding"] += 1
    # Independent affine group law checks projective Montgomery sequences.
    for p in (101, 103, 107, 109):
        for a24 in (2, 3, 5):
            A = (4*a24-2) % p
            x0 = 7
            rhs = (x0**3+A*x0*x0+x0) % p
            # Curve twist rhs*y^2=x^3+A*x^2+x, with point (7,1).
            if rhs == 0:
                continue
            def affine_add(P, Q):
                if P is None:
                    return Q
                if Q is None:
                    return P
                x, y = P
                v, w = Q
                if x == v and (y+w) % p == 0:
                    return None
                if P == Q:
                    slope = (3*x*x+2*A*x+1)*pow(2*rhs*y, -1, p) % p
                else:
                    slope = (w-y)*pow(v-x, -1, p) % p
                xx = (rhs*slope*slope-A-x-v) % p
                return xx, (-y+slope*(x-xx)) % p

            base, oracle = (x0, 1), None
            for k in range(1, 80):
                oracle = affine_add(oracle, base)
                projective = montgomery_scale((x0, 1), k, a24, p)
                if oracle is None:
                    assert projective[1] % p == 0
                else:
                    assert projective[0]*pow(projective[1], -1, p) % p == oracle[0]
                checks["curve_points"] += 1
    return checks


def controls():
    rows = []
    for p, q in ((6827, 7187), (2346272483, 3649327547),
                 (661911275027, 720957498683)):
        n = p*q
        tests = {}
        for name, function in (("linear_same_colour", lambda: QUADRATIC["factor_quadratic"](n, order_divisor=1, discriminant=-1)),
                               ("dickson6_same_colour", lambda: factor_dickson(n)),
                               ("curve", lambda: curve_extract(n))):
            began = time.perf_counter()
            result = function()
            elapsed = 1000*(time.perf_counter()-began)
            assert result["factor"] in (None, p, q)
            tests[name] = {"result": result, "ms": elapsed}
        # Reference order used here only to diagnose a recovered witness.
        alias = tests["dickson6_same_colour"]["result"]
        if alias["factor"]:
            f = alias["factor"]
            order = (f+1)//12
            ring = QUADRATIC["QuadraticRing"](f, -1)
            assert gmpy2.is_prime(order)
            assert ring.power(tuple(alias["projected_base"]), order) == (1, 0)
            assert order > alias["linear_cover"]
            alias["reference_order_after_recovery"] = order
            alias["order_to_old_cover_ratio"] = order/alias["linear_cover"]
        assert tests["linear_same_colour"]["result"]["factor"] is None
        assert tests["curve"]["result"]["factor"] in (p, q)
        for staged in (True, False):
            check = curve_extract(n, max_curves=1, staged=staged)
            assert check["factor"] in (p, q)
        rows.append({"N_decimal": str(n), "reference_factors_decimal": [str(p), str(q)],
                     "tests": tests})
    return {"controls": rows, "source_hashes": source_hashes(),
            "interpretation": "Nonlinear aliases hit two controls; changing to ECM hits all three. "
                              "Neither is a generic deterministic one-sixth guarantee."}


def benchmark(bits, cases, repeats, seed):
    rng = random.Random(seed)
    rows = []
    for bit_count in bits:
        half = bit_count//2
        samples = []
        for _ in range(cases):
            p = int(gmpy2.next_prime(rng.randrange(1 << (half-1), (1 << half)-100)))
            q = int(gmpy2.next_prime(rng.randrange(1 << (half-1), (1 << half)-100)))
            while q == p:
                q = int(gmpy2.next_prime(q+2))
            n = p*q
            timings = {"linear": [], "dickson6": [], "curve": [], "curve_full": []}
            results = {}
            for _ in range(repeats):
                names = list(timings)
                rng.shuffle(names)
                for name in names:
                    functions = {"linear": lambda: QUADRATIC["factor_quadratic"](n, order_divisor=1, discriminant=-1),
                                 "dickson6": lambda: factor_dickson(n),
                                 "curve": lambda: curve_extract(n, max_curves=1),
                                 "curve_full": lambda: curve_extract(n, max_curves=1, staged=False)}
                    started = time.perf_counter()
                    result = functions[name]()
                    timings[name].append(1000*(time.perf_counter()-started))
                    assert result["factor"] in (None, p, q)
                    results[name] = result
            samples.append({"N_decimal": str(n), "reference_factors_decimal": [str(p), str(q)],
                            "results": results, "median_ms": {k: statistics.median(v) for k, v in timings.items()}})
        rows.append({"nominal_bits": bit_count, "samples": samples,
                     "hits": {name: sum(s["results"][name]["factor"] is not None for s in samples) for name in timings},
                     "total_median_ms": {name: sum(s["median_ms"][name] for s in samples) for name in timings},
                     "nonlinear_extra_hits": sum(s["results"]["linear"]["factor"] is None and s["results"]["dickson6"]["factor"] is not None for s in samples)})
    return {"seed": seed, "cases_per_size": cases, "repeats": repeats,
            "rows": rows, "source_hashes": source_hashes(),
            "timing_scope": "Randomized warm-module full calls; includes all query-specific projections, "
                            "curves, points and polynomial work; excludes imports/sample generation/JSON."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("validate", "controls", "factor", "benchmark"))
    parser.add_argument("n", nargs="?", type=int)
    parser.add_argument("--algorithm", choices=("dickson", "curve"), default="dickson")
    parser.add_argument("--bits", type=int, nargs="+", default=[48, 64, 80])
    parser.add_argument("--cases", type=int, default=16)
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--seed", type=int, default=2026100663)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.mode == "validate":
        out = {"checks": validate(), "source_hashes": source_hashes()}
    elif args.mode == "controls":
        out = controls()
    elif args.mode == "benchmark":
        out = benchmark(args.bits, args.cases, args.repeats, args.seed)
    elif args.n is None:
        parser.error("factor requires n")
    else:
        out = (factor_dickson if args.algorithm == "dickson" else curve_extract)(args.n)
    encoded = json.dumps(safe_json(out), indent=2)+"\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
