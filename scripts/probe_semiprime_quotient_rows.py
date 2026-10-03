#!/usr/bin/env python3
"""Public Euclidean quotient rows and one-dimensional collision evaluation.

The balanced search still has an explicit m+sqrt(N)/m^(3/2) budget.
Native counters are not a complete bit-machine certificate. Private factors
enter only the separately labelled reference validations.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import random
import runpy
import time

import gmpy2

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-known-bits-budget-audit.json"
REPLAY_ID = 202610032801
NORM = runpy.run_path(str(ROOT/"scripts/probe_semiprime_multiplier_norm.py"))
ScalarLedger, BATCH = NORM["ScalarLedger"], NORM["BATCH"]


class IntegerLedger:
    """Charge literal integer construction, including every inverse division.

    Operand-bit traffic is diagnostic; this is not a proved Boolean circuit.
    """
    def __init__(self):
        self.counts = Counter()
        self.operand_bits = self.max_integer_bits = 0

    def charge(self, kind, *values):
        self.counts[kind] += 1
        sizes = [max(1, abs(int(x)).bit_length()) for x in values]
        self.operand_bits += sum(sizes)
        self.max_integer_bits = max([self.max_integer_bits]+sizes)

    def mul(self, a, b):
        self.charge("integer_products", a, b)
        result = a*b
        self.max_integer_bits = max(self.max_integer_bits, abs(result).bit_length())
        return result

    def add(self, a, b):
        self.charge("integer_additions", a, b)
        return a+b

    def divmod(self, a, b):
        self.charge("integer_divmod", a, b)
        return divmod(a, b)

    def gcd(self, a, b):
        self.charge("integer_gcd", a, b)
        return math.gcd(a, b)

    def inverse(self, a, m):
        self.charge("public_inverses", a, m)
        r0, r1, t0, t1 = a, m, 1, 0
        while r1:
            q, r = self.divmod(r0, r1)
            r0, r1, t0, t1 = r1, r, t1, self.add(t0, -self.mul(q, t1))
        if r0 != 1:
            raise ValueError("public inverse requires coprime inputs")
        return t0

    def sqrt(self, n):
        self.charge("integer_square_roots", n)
        return math.isqrt(n)

    def root(self, n, degree):
        self.charge("integer_root_calls", n, degree)
        return int(gmpy2.iroot(n, degree)[0])

    def power(self, a, exponent):
        result = 1
        for _ in range(exponent):
            result = self.mul(result, a)
        return result

    def stats(self):
        return dict(self.counts, integer_operand_bit_traffic=self.operand_bits,
                    max_integer_bits=self.max_integer_bits)


def short_pair(m, u, threshold, integers):
    """Same signed Euclidean recurrence as Lean's euclidShort."""
    r0, r1, x, y, negative, divisions = m, integers.divmod(u, m)[1], 0, 1, False, 0
    while r1 > threshold:
        quotient, remainder = integers.divmod(r0, r1)
        r0, r1, x, y = r1, remainder, y, integers.add(x, integers.mul(quotient, y))
        negative, divisions = not negative, divisions+1
    return (-r1 if negative else r1), y, divisions


def public_row(n, m, j, integers, threshold=None):
    """Only public N, m and residue j enter this constructor."""
    threshold = integers.sqrt(m) if threshold is None else threshold
    inverse = integers.inverse(j, m)
    inverse_square = integers.mul(inverse, inverse)
    u = integers.divmod(integers.mul(n, inverse_square), m)[1]
    a, t, steps = short_pair(m, u, threshold, integers)
    j_square = integers.mul(j, j)
    d_numerator = integers.add(integers.mul(n, t), -integers.mul(j_square, a))
    d, rem = integers.divmod(d_numerator, m)
    assert rem == 0
    half = integers.divmod(m, 2)[0]
    shifted = integers.add(-integers.mul(inverse, d), half)
    b = integers.add(integers.divmod(shifted, m)[1], -half)
    c, rem = integers.divmod(integers.add(d, integers.mul(j, b)), m)
    assert rem == 0
    m_square = integers.mul(m, m)
    one_minus_j = integers.add(1, -j)
    exponent = integers.add(integers.add(integers.mul(c, m_square),
        integers.mul(integers.mul(b, m), one_minus_j)),
        integers.mul(a, integers.mul(one_minus_j, one_minus_j)))
    return dict(j=j, a=a, b=b, c=c, t=t, divisions=steps, exponent=exponent)


def index_length(n, m, integers):
    s, height = integers.sqrt(m), integers.add(integers.sqrt(n), 1)
    axis = integers.add(integers.mul(3, height), integers.mul(2, m))
    tail = integers.mul(integers.add(integers.divmod(m, 2)[0], 1), m)
    numerator = integers.add(integers.mul(s, axis), tail)
    return integers.add(integers.divmod(numerator, integers.mul(m, m))[0], 1)


def integer_roots(n, m, row, index, integers):
    """Both quadratic orientations, followed by public divisor validation."""
    a, b, j, t = (row[k] for k in ("a", "b", "j", "t"))
    linear = integers.add(integers.add(integers.mul(b, m),
        -integers.mul(integers.mul(2, a), j)),
        -integers.mul(integers.mul(m, m), index))
    constant = integers.mul(t, n)
    discriminant = integers.add(integers.mul(linear, linear),
        -integers.mul(integers.mul(4, a), constant))
    if discriminant < 0:
        return []
    root = integers.sqrt(discriminant)
    if integers.mul(root, root) != discriminant:
        return []
    denominator = integers.mul(2, a)
    result = []
    for numerator in (integers.add(-linear, root), integers.add(-linear, -root)):
        candidate, remainder = integers.divmod(numerator, denominator)
        if remainder == 0 and 1 < candidate < n and integers.divmod(n, candidate)[1] == 0:
            result.append(candidate)
    return result


def public_source(n, scaling=6, alpha=2):
    """N-only balanced-search prototype, including all public construction.

    A saturated local-period setup is reported as inconclusive. The square,
    GCD, row, power and polynomial stages all occur inside the timer.
    """
    start = time.perf_counter()
    integers, ring, batch = IntegerLedger(), ScalarLedger(n), BATCH["MonicBatch"](n)
    metrics = Counter()
    rows, remaining, points, values = [], [], [], []
    m, length = None, None

    def finish(factor, stage, witness=None):
        return dict(N=n, scaling=scaling, modulus=m, index_length=length,
            factor=factor, stage=stage, witness=witness,
            constructed_rows=len(rows), remaining_giant_steps=len(remaining),
            baby_points=len(points), evaluated_points=len(values),
            milliseconds=1000*(time.perf_counter()-start),
            metrics=dict(metrics, **integers.stats(), **ring.stats(), **batch.stats()),
            constructed_pair_matrix=False, is_complete_bit_certificate=False)

    square = integers.sqrt(n)
    if integers.mul(square, square) == n and 1 < square < n:
        return finish(square, "public-square")
    root = integers.root(n, 2*scaling)
    root_power = integers.power(root, 2*scaling)
    if root_power != n:
        root = integers.add(root, 1)
    m = integers.mul(root, root)
    if m <= 1:
        return finish(None, "inconclusive-small-modulus")
    common = integers.gcd(m, n)
    if 1 < common < n:
        return finish(common, "public-modulus-gcd")
    if common != 1:
        return finish(None, "inconclusive-modulus")
    common = integers.gcd(alpha, n)
    if 1 < common < n:
        return finish(common, "public-base-gcd")
    if common != 1:
        return finish(None, "inconclusive-base")
    length = index_length(n, m, integers)
    m_square = integers.mul(m, m)
    gamma = ring.power(alpha, m_square)
    points.append(1)
    for i in range(1, length):
        point = ring.mul(points[-1], gamma)
        points.append(point)
        common = integers.gcd(point-1, n)
        metrics["local_period_checks"] += 1
        if 1 < common < n:
            return finish(common, "public-local-period-gcd", dict(index=i))
        if common == n:
            return finish(None, "inconclusive-saturated-local-period", dict(index=i))
    lookup = {point: i for i, point in enumerate(points)}
    assert len(lookup) == len(points)
    threshold = integers.sqrt(m)
    inverse = integers.divmod(integers.inverse(alpha, n), n)[1]
    for j in range(1, m):
        if integers.gcd(j, m) != 1:
            continue
        row = public_row(n, m, j, integers, threshold)
        rows.append(row)
        for orientation in (1, -1):
            exponent = orientation*row["exponent"]
            integers.charge("integer_sign_orientations", row["exponent"])
            value = ring.power(alpha if exponent >= 0 else inverse, abs(exponent))
            metrics["giant_lookup_queries"] += 1
            if value in lookup:
                metrics["global_matches"] += 1
                index = orientation*lookup[value]
                factors = integer_roots(n, m, row, index, integers)
                metrics["quadratic_recovery_calls"] += 1
                if factors:
                    return finish(factors[0], "global-quadratic",
                        dict(row=row, index=index, orientation=orientation))
                metrics["removed_global_giant_steps"] += 1
            else:
                remaining.append(dict(value=value, row=row, orientation=orientation))
    if not remaining:
        return finish(None, "inconclusive-empty-giant-list")
    polynomial = batch.tree([target["value"] for target in remaining])[0]
    values = batch.evaluate(polynomial, points)
    metrics["root_polynomials"] += 1
    metrics["point_trees"] += 1
    metrics["explicit_input_count"] = len(remaining)+len(points)
    for i, value in enumerate(values):
        common = integers.gcd(value, n)
        metrics["aggregate_gcd_queries"] += 1
        if 1 < common < n:
            return finish(common, "one-axis-product", dict(index=i))
        if common == n:
            for target in remaining:
                difference = (points[i]-target["value"]) % n
                metrics["constructed_selected_column_differences"] += 1
                common = integers.gcd(difference, n)
                metrics["selected_column_gcd_queries"] += 1
                assert common != n, "global matches must have been removed"
                if 1 < common < n:
                    return finish(common, "selected-column-gcd", dict(index=i,
                        row=target["row"], orientation=target["orientation"]))
            raise AssertionError("saturated aggregate must retain a proper residual")
    return finish(None, "inconclusive-no-collision")


def reference_row_case(p, q, m):
    """Private factors enter only this explicitly labelled validation."""
    n, j, integers = p*q, p % m, IntegerLedger()
    if math.gcd(m, n) != 1:
        return None
    row = public_row(n, m, j, integers)
    a, b, c, t = (row[k] for k in ("a", "b", "c", "t"))
    x = p//m
    assert m*m*c-j*m*b+j*j*a == n*t
    assert a != 0 and abs(a) <= math.isqrt(m) and 0 < t <= math.isqrt(m)
    assert abs(b) <= m//2+1 and row["divisions"] <= 2*m.bit_length()
    polynomial_value = a*x*x+b*x+c
    assert polynomial_value % p == 0
    index = polynomial_value//p
    length = index_length(n, m, integers)
    assert abs(index) < length
    assert m*m*index == a*p+b*m-2*a*j+t*q
    assert p in integer_roots(n, m, row, index, integers)
    assert pow(2, row["exponent"] % (p-1), p) == pow(2, (m*m*index) % (p-1), p)
    return dict(N=n, reference_p=p, reference_q=q, m=m, row=row,
        reference_index=index, index_length=length,
        recovered_candidates=integer_roots(n, m, row, index, integers),
        constructor_metrics=integers.stats())


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "RiemannGaussian/SemiprimeQuotientRows.lean",
        "scripts/CheckSemiprimeQuotientRows.lean", "scripts/probe_semiprime_quotient_rows.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import primerange
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = source_inventory()
    rnd, primes, cases = random.Random(REPLAY_ID), list(primerange(101, 5000)), []
    relation_cases, maximum_divisions = 0, 0
    for m in range(2, 258):
        for u in range(1, m):
            if math.gcd(m, u) != 1:
                continue
            a, t, divisions = short_pair(m, u, math.isqrt(m), IntegerLedger())
            assert a != 0 and abs(a) <= math.isqrt(m) and 0 < t <= math.isqrt(m)
            assert (a-u*t) % m == 0 and divisions <= 2*m.bit_length()
            relation_cases += 1
            maximum_divisions = max(maximum_divisions, divisions)
    while len(cases) < 192:
        p, q = sorted(rnd.sample(primes, 2))
        if q > 2*p:
            continue
        m = rnd.randint(2, 1000)
        case = reference_row_case(p, q, m)
        if case is not None:
            cases.append(case)
    small_sources, outcomes = [], Counter()
    for case in cases[:128]:
        source = public_source(case["N"])
        if source["factor"] is not None:
            assert source["factor"] in (case["reference_p"], case["reference_q"])
        outcomes[source["stage"]] += 1
        small_sources.append(source)
    controls = [reference_row_case(101, 103, 4),
        reference_row_case(1000000007, 1400000543, 1089),
        reference_row_case(1000000007, 1400000543, 4356)]
    large_sources = []
    for scaling in (6, 5):
        source = public_source(1000000007*1400000543, scaling)
        assert source["factor"] in (1000000007, 1400000543)
        large_sources.append(source)
        print(json.dumps(dict(progress="large-public-source", scaling=scaling,
            factor=source["factor"], stage=source["stage"],
            modulus=source["modulus"], index_length=source["index_length"],
            milliseconds=source["milliseconds"])), flush=True)
    shape_checks = []
    for root in (2, 4, 8, 16, 32, 64):
        m = root*root
        fifth = index_length(root**10, m, IntegerLedger())
        sixth = index_length(root**12, m, IntegerLedger())
        assert 2*m+fifth <= 12*m+1
        shape_checks.append(dict(square_modulus_root=root, m=m,
            fifth_N=root**10, fifth_baby_length=fifth, fifth_input_envelope=2*m+fifth,
            sixth_N=root**12, sixth_baby_length=sixth, sixth_input_envelope=2*m+sixth))
    assert source_inventory() == sources, "source changed during replay"
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Public Euclidean quotient-row construction and balanced collision coverage",
        one_sixth_guarantee="OPEN", is_complete_semiprime_factorizer=False,
        is_bit_complexity_certificate=False, is_formal_machine_refinement=False,
        universal_row_constructor_lean=True, balanced_collision_index_coverage_lean=True,
        validation=dict(short_relations=relation_cases, maximum_relation_divisions=maximum_divisions,
            balanced_reference_rows=len(cases), small_public_sources=len(small_sources),
            small_public_outcomes=dict(outcomes), large_public_sources=len(large_sources),
            exact_controls=len(controls), shape_checks=len(shape_checks),
            private_factors_used_only_as_references=True),
        controls=controls, cases=cases, small_public_sources=small_sources,
        large_public_sources=large_sources, shape_checks=shape_checks,
        primary_lead="https://eprint.iacr.org/2025/1004.pdf",
        limitations="The public row, bounded balanced-case integer index, exact Fermat collision and quadratic candidate completeness are proved in Lean. The native source is an N-only balanced-case prototype; a saturated local-period setup remains inconclusive. It is not a complete universal factorizer or a formal bit-machine refinement. The explicit m+sqrt(N)/m^(3/2) search budget balances at N^(1/5); the sixth-root modulus still has an N^(1/4) certified baby-axis envelope. These layout bounds are not lower bounds on all algorithms or on every actual collision index. All timed public-source work, including square/root setup, Bezout inverses, Euclidean division, powers, polynomial and GCD work, occurs inside its timer. Reference-factor diagnostics are separate. The complete every-run arbitrary-ratio one-sixth bit theorem remains open.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), validation=report["validation"],
        controls=controls, large_public_sources=large_sources,
        shape_checks=shape_checks, one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
