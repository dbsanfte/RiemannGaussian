#!/usr/bin/env python3
"""Diagnostic long-period probes, kept separate from public-input extraction.

Private-order tables below are explicitly reference-only experiments. The
actual factor_dickson/curve_extract algorithms never consult these tables.
"""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import runpy
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
LONG = runpy.run_path(str(ROOT / "scripts/probe_semiprime_long_period.py"))
SINGLE = LONG["SINGLE"]
CONTROLS = ((6827, 7187), (2346272483, 3649327547),
            (661911275027, 720957498683))


def dickson_mod(x, degree, parameter, modulus):
    a, b = 2, x % modulus
    for _ in range(1, degree):
        a, b = b, (x*b-parameter*a) % modulus
    return a if degree == 0 else b


def aliases(period, width, mode, degree, parameter=1):
    f = (lambda x: pow(x, degree, period)) if mode == "power" else (
        lambda x: dickson_mod(x, degree, parameter, period))
    table = {}
    for i in range(width):
        v = f(i)
        table[v] = (i, 1)
        table[-v % period] = (i, -1)
    hits = []
    for j in range(1, width+1):
        v = f(width*j)
        if v in table:
            hits.append([j, *table[v]])
    return {"count": len(hits), "first": hits[0] if hits else None}


def reference_phases(n):
    """Predetermined public exponents, evaluated only in a private-order audit."""
    return list(dict.fromkeys([0]+[sign*k for k in range(1, 17) for sign in (1, -1)]
                             +[sign*2**k for k in range(5, 17) for sign in (1, -1)]
                             +[n, -n, n//2, -n//2, n//3, -n//3]))


def reference_phase_aliases(period, width, n):
    baby = {dickson_mod(i, 6, 1, period): i for i in range(width)}
    target = [(j, dickson_mod(width*j, 6, 1, period)) for j in range(1, width+1)]
    hits = []
    phases = reference_phases(n)
    for c in phases:
        for j, value in target:
            wanted = (-value-2*c) % period
            if wanted in baby:
                hits.append({"phase_exponent_decimal": str(c), "giant_index": j,
                             "baby_index": baby[wanted]})
                break
    return {"phase_count": len(phases), "inverse_channel_hits": hits,
            "phase_exponents_decimal": [str(c) for c in phases]}


def reference_orbit_aliases(period, width, n):
    hits = []
    for a, b in ((2, 3), (2, 5), (3, 5), (2, n), (2, n+1), (n-1, n+1), (n, n+1)):
        baby, value = {}, 1
        for i in range(1, width+1):
            value = value*a % period
            baby.setdefault(value, (i, "equal"))
            baby.setdefault(-value % period, (i, "inverse"))
        value = 1
        for j in range(1, width+1):
            value = value*b % period
            if value in baby:
                i, channel = baby[value]
                hits.append({"bases_decimal": [str(a), str(b)], "baby_index": i,
                             "giant_index": j, "channel": channel})
                break
    return {"tested_pairs": 7, "hits": hits}


def finite_field_fibers():
    """Full small reference fields, not the truncated input-specific grids."""
    rows, checks = [], 0
    for p in SINGLE["primes_upto"](1000):
        if p < 101:
            continue
        values = [dickson_mod(x, 6, 1, p) for x in range(p)]
        counts = Counter(values)
        power = Counter(pow(x, 6, p) for x in range(p))
        predicted = (p-1)//(2*math.gcd(6, p-1))+(p+1)//(2*math.gcd(6, p+1))+1
        assert len(counts) == predicted and max(counts.values()) <= 6
        for u in range(1, p):
            inverse = pow(u, -1, p)
            assert dickson_mod((u+inverse) % p, 6, 1, p) == (pow(u, 6, p)+pow(inverse, 6, p)) % p
            checks += 1
        rows.append({"prime": p, "gcd_degree_period_minus_one": math.gcd(6, p-1),
                     "gcd_degree_period_plus_one": math.gcd(6, p+1),
                     "dickson_image_size": len(counts), "predicted_image_size": predicted,
                     "dickson_fiber_histogram": dict(sorted(Counter(counts.values()).items())),
                     "dickson_ordered_collision_pairs": sum(c*c for c in counts.values()),
                     "power_ordered_collision_pairs": sum(c*c for c in power.values())})
    groups = []
    for residue in (1, 5):
        group = [row for row in rows if row["prime"] % 6 == residue]
        gains = [row["dickson_ordered_collision_pairs"]/row["power_ordered_collision_pairs"] for row in group]
        groups.append({"prime_mod_6": residue, "fields": len(group),
                       "uniform_full_field_collision_ratio_dickson_over_power_min": min(gains),
                       "uniform_full_field_collision_ratio_dickson_over_power_max": max(gains)})
    return {"field_count": len(rows), "trace_lift_identity_checks": checks, "groups": groups,
            "full_field_rows": rows,
            "scope": "Exact complete small-field counts. A uniform full-field collision ratio "
                     "is not a coverage theorem for the actual short structured input grids."}


def reference_rough_order_geometry():
    """Classify cardinality envelopes using saved factors, never during recovery."""
    import sympy
    corpus = ROOT / "docs/semiprime-long-period-benchmark.json"
    benchmark = json.loads(corpus.read_text())
    rows, counts = [], Counter()
    for row in benchmark["rows"]:
        for sample in row["samples"]:
            n = int(sample["N_decimal"])
            p = min(int(x) for x in sample["reference_factors_decimal"])
            bound = SINGLE["ceil_root"](n, 6)
            assert p <= bound**3
            small = SINGLE["primes_upto"](bound)
            geometries = []
            for offset in (-1, 1):
                rough = p+offset
                for prime in small:
                    while rough % prime == 0:
                        rough //= prime
                factors = {int(r): int(e) for r, e in sympy.factorint(rough).items()}
                multiplicity = sum(factors.values())
                assert multiplicity <= 2
                assert all(r > bound for r in factors)
                if multiplicity == 2:
                    assert all(r < bound*bound for r in factors)
                kind = ("cleared" if rough == 1 else "inside_old_cover" if rough <= bound*bound
                        else "single_long_prime" if multiplicity == 1
                        else "two_rough_factors" if len(factors) == 2 else "rough_prime_square")
                counts[kind] += 1
                geometries.append({"group_offset": offset, "rough_cardinality_decimal": str(rough),
                                   "reference_factors": [[str(r), e] for r, e in factors.items()],
                                   "class": kind})
            rows.append({"N_decimal": str(n), "B": bound, "smaller_prime_group_envelopes": geometries})
    return {"groups": sum(counts.values()), "class_counts": dict(counts), "rows": rows,
            "corpus_sha256": hashlib.sha256(corpus.read_bytes()).hexdigest(),
            "scope": "Reference-only factorization of p-1,p+1, for the smaller prime in a saved corpus. "
                     "An actual projected element order can be a proper divisor of this envelope. "
                     "Algorithms receive none of these factorizations."}


def report(check_lean=False):
    proof = ROOT / "RiemannGaussian/SemiprimeLongPeriodExtraction.lean"
    formal = {"file": str(proof.relative_to(ROOT)),
              "sha256": hashlib.sha256(proof.read_bytes()).hexdigest(),
              "scope": "Trace/factorisation/finite-difference/remainder algebra and exact integer witnesses; "
                       "not a full implementation or generic complexity proof."}
    if check_lean:
        lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
        result = subprocess.run([lake, "env", "lean", str(proof.relative_to(ROOT))],
                                cwd=ROOT, capture_output=True, text=True, check=False)
        formal.update({"returncode": result.returncode, "output": result.stdout+result.stderr})
        assert result.returncode == 0 and formal["output"] == "", formal
    public, reference = [], []
    for p, q in CONTROLS:
        n = p*q
        started = time.perf_counter()
        scalar = SINGLE["factor_projected"](n, order_divisor=1)
        alpha = scalar["projected_base"]
        cyclotomic_hits = []
        for d in range(1, 65):
            g = math.gcd(pow(alpha, n**d-1, n)-1, n)
            if 1 < g < n:
                cyclotomic_hits.append({"degree": d, "factor": g})
        trace = (pow(2, n-1, n)+pow(pow(2, -1, n), n-1, n)) % n
        expected = (pow(2, q-p, n)+pow(pow(2, -1, n), q-p, n)) % n
        assert trace == expected
        public.append({"N_decimal": str(n), "cyclotomic_degrees": [1, 64],
                       "cyclotomic_hits": cyclotomic_hits,
                       "public_reciprocal_gap_trace": trace,
                       "ms_including_projection_and_trace": 1000*(time.perf_counter()-started)})
        width = scalar["bound"]
        entries = []
        for prime in (p, q):
            for period in ((prime-1)//2, (prime+1)//12):
                tests = []
                for degree in (1, 2, 3, 4, 6, 8, 12, 16, 24, 30, 60):
                    hit = aliases(period, width, "power", degree)
                    if hit["count"]:
                        tests.append({"map": "power", "degree": degree, **hit})
                for degree in (4, 6, 12, 30):
                    for parameter in (-1, 1):
                        hit = aliases(period, width, "dickson", degree, parameter)
                        if hit["count"]:
                            tests.append({"map": "dickson", "degree": degree,
                                          "parameter": parameter, **hit})
                same_sign = next((t for t in tests if t["map"] == "dickson"
                                  and t["degree"] == 6 and t["parameter"] == 1
                                  and t["first"][2] == 1), None)
                lift_characters = None
                if same_sign:
                    j, i, _ = same_sign["first"]
                    assert LONG["gmpy2"].is_prime(period)
                    lift_characters = [int(LONG["gmpy2"].legendre(x*x-4, period))
                                       for x in (width*j, i)]
                entries.append({"reference_period": period,
                                "gcd_degree6_period_minus_one": math.gcd(6, period-1),
                                "gcd_degree6_period_plus_one": math.gcd(6, period+1),
                                "hit_maps": tests,
                                "same_sign_dickson6_trace_lift_characters": lift_characters,
                                "reference_only_phase_audit": reference_phase_aliases(period, width, n),
                                "reference_only_orbit_audit": reference_orbit_aliases(period, width, n)})
        reference.append({"N_decimal": str(n), "width": width,
                          "reference_gap": q-p, "gap_in_B_squared": q-p <= width*width,
                          "private_period_diagnostic": entries})
    files = [Path(__file__), ROOT / "scripts/probe_semiprime_long_period.py"]
    return {"public_input_probes": public,
            "reference_only_alias_probes": reference,
            "finite_field_fiber_audit": finite_field_fibers(),
            "reference_only_rough_order_geometry": reference_rough_order_geometry(),
            "reference_scope": "Private periods diagnose the maps only. Recovery receives N, "
                               "public colour/degree/budget and no reference tables.",
            "exact_checks": LONG["validate"](), "formal_proof": formal,
            "source_hashes": {str(f.relative_to(ROOT)): hashlib.sha256(f.read_bytes()).hexdigest() for f in files}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-lean", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    encoded = json.dumps(LONG["safe_json"](report(args.check_lean)), indent=2)+"\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
