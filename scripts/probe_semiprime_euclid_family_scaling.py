#!/usr/bin/env python3
"""Reference-only index growth for the full intermediate-row family.

Private factors select the two correct residue packets and evaluate their
actual integer indices. This is an exact diagnostic, NOT an N-only source,
complete detector replay, bit-clock certificate, or asymptotic lower bound.
The companion EuclidRowFamily module checks one complete-family control.
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

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-euclid-row-family-audit.json"
REPLAY_ID = 202610033002
FAMILY = runpy.run_path(str(ROOT/"scripts/probe_semiprime_euclid_row_family.py"))


def residue_packets(n, m, j, integers):
    """Public N,m,j determine these packets; selecting j is reference-only."""
    L, U, V = FAMILY["PARENT"]["public_box"](n, integers)
    inverse = integers.inverse(j, m)
    slope = integers.divmod(integers.mul(n, integers.mul(inverse, inverse)), m)[1]
    square, half = integers.mul(m, m), integers.divmod(m, 2)[0]
    for a, t in FAMILY["public_pairs"](m, slope, integers, Counter()):
        d, rem = integers.divmod(integers.add(integers.mul(n, t),
            -integers.mul(integers.mul(j, j), a)), m)
        assert rem == 0
        b = integers.add(integers.divmod(integers.add(-integers.mul(inverse, d), half), m)[1], -half)
        c, rem = integers.divmod(integers.add(d, integers.mul(j, b)), m)
        assert rem == 0
        v = integers.add(integers.mul(b, m), -integers.mul(integers.mul(2, a), j))
        assert m*m*c-j*m*b+j*j*a == n*t
        for orientation, lo, hi in (
            ("smaller-factor", a*(L if a >= 0 else U)+t*U+v,
                a*(U if a >= 0 else L)+t*V+v),
            ("larger-factor", t*L+a*(U if a >= 0 else V)+v,
                t*U+a*(V if a >= 0 else U)+v)):
            shift = (lo+hi+square)//(2*square)
            yield dict(j=j, a=a, b=b-shift*m, c=c-shift*j, t=t,
                shift=shift, orientation=orientation, exponent=t*n+a+v-shift*square)


def reference_case(p, q, nominal_bits):
    n, integers, metrics = p*q, FAMILY["IntegerLedger"](), Counter()
    assert p <= q <= 2*p
    m = FAMILY["first_public_prime"](n, integers, metrics)
    assert math.gcd(n, m) == 1
    best, count = None, 0
    for factor in (p, q):
        for packet in residue_packets(n, m, factor % m, integers):
            a, b, c = (packet[k] for k in ("a", "b", "c"))
            quotient = factor//m
            value = a*quotient*quotient+b*quotient+c
            assert value % factor == 0
            index = value//factor
            assert (packet["exponent"]-m*m*index) % (factor-1) == 0
            count += 1
            if best is None or abs(index) < abs(best["index"]):
                best = dict(packet, factor=factor, index=index)
    return dict(N=n, nominal_bits=nominal_bits, input_bits=n.bit_length(),
        reference_p=p, reference_q=q, public_modulus=m, correct_residue_packets=count,
        minimum_abs_index=abs(best["index"]), best_reference_packet=best,
        tested_reference_constructor_metrics=integers.stats(),
        public_modulus_metrics=dict(metrics), is_N_only_source=False)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "scripts/probe_semiprime_euclid_family_scaling.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime, isprime
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources, rnd, cases, summaries = source_inventory(), random.Random(REPLAY_ID), [], []
    for bits in (48, 64, 80, 96, 112, 128):
        band = []
        for _ in range(32):
            p = int(nextprime(rnd.randrange(2**(bits//2-1), 2**(bits//2))))
            q = int(nextprime(rnd.randrange(11*p//10, 19*p//10)))
            assert isprime(p) and isprime(q)
            band.append(reference_case(p, q, bits))
        worst = max(band, key=lambda c: c["minimum_abs_index"]/c["public_modulus"])
        summary = dict(nominal_bits=bits, cases=len(band),
            worst_index=worst["minimum_abs_index"], worst_modulus=worst["public_modulus"],
            worst_N=worst["N"], worst_reference_p=worst["reference_p"],
            worst_reference_q=worst["reference_q"],
            windows_missed={str(C): sum(c["minimum_abs_index"] > C*c["public_modulus"] for c in band)
                for C in (1, 2, 4, 8, 16, 32, 64)})
        cases.extend(band)
        summaries.append(summary)
        print(json.dumps(dict(progress="reference-only-index-band", **summary)), flush=True)
    assert source_inventory() == sources
    report = dict(replay_id=REPLAY_ID, source_sha256=sources,
        scope="Reference-only correct-residue index growth; no complete detector claim",
        is_N_only_source=False, is_factorization_runtime_measurement=False,
        is_bit_complexity_certificate=False, is_asymptotic_lower_bound=False,
        one_sixth_guarantee="OPEN", summaries=summaries, cases=cases,
        limitations="These exact native diagnostics select correct residues using private factors and evaluate every intermediate packet at those factors. They are not an N-only factorizer, do not inspect all incorrect-residue aliases at large sizes, and do not prove detector failure or an unbounded asymptotic ratio. All factor generation and primality checks are native reference work, not Lean prime certificates for these 192 larger cases. Counters price only the tested residue constructors and public modulus choice; they do not price a full public family, Boolean refinement or complete factorizer. The companion compiled control independently proves one complete public-family failure. These data motivate a new coverage argument instead of claiming that any fixed multiple of m or all one-sixth algorithms are impossible.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), reference_cases=len(cases),
        summaries=summaries, one_sixth_guarantee="OPEN"), indent=2))


if __name__ == "__main__":
    main()
