#!/usr/bin/env python3
"""Reference-only rare-pair labels and a wider combined-channel corpus.

Private full component orders are diagnostic inputs. This runs neither a
public source nor a bit-cost measurement and does not produce Lean proofs.
The preceding classifier and all earlier sources remain hash-frozen.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import random
import runpy

ROOT = Path(__file__).resolve().parents[1]
PARENT_AUDIT = "docs/semiprime-combined-row-coverage-audit.json"
REPLAY_ID = 202610033202
COVERAGE = runpy.run_path(str(ROOT/"scripts/probe_semiprime_combined_row_coverage.py"))
DERIVATIVE = COVERAGE["DERIVATIVE"]


def rare_pairs(p, q):
    """Retain exact original packet labels for every non-global folded hit."""
    from sympy import n_order
    n, integers, metrics = p*q, DERIVATIVE["IntegerLedger"](), {}
    # The first-public-prime routine charges into a Counter.
    from collections import Counter
    metrics = Counter()
    m = DERIVATIVE["FAMILY"]["first_public_prime"](n, integers, metrics)
    orders = [int(n_order(2, p)), int(n_order(2, q))]
    period = math.lcm(*orders)
    orbits, seen, pairs, wanted = set(), [{}, {}], [], set()
    for packet in DERIVATIVE["reference_packets"](n, m):
        e = packet["exponent"]
        whole = e % period
        orbit = min(whole, (-whole) % period)
        if orbit in orbits:
            continue
        orbits.add(orbit)
        for axis, order in enumerate(orders):
            residue = e % order
            fold = min(residue, (-residue) % order)
            if fold in seen[axis]:
                other = seen[axis][fold]
                channel = "ordinary" if (e-other) % order == 0 else "reciprocal"
                pairs.append(dict(reference_factor=[p, q][axis], order=order,
                    channel=channel, exponent=e, other_exponent=other,
                    order_multiple=(e-other if channel == "ordinary" else e+other)//order))
                wanted.update((e, other))
            seen[axis][fold] = e
    del orbits, seen
    labels = {}
    for packet in DERIVATIVE["reference_packets"](n, m):
        if packet["exponent"] in wanted:
            labels.setdefault(packet["exponent"], []).append(packet)
    for pair in pairs:
        pair["packets"] = labels[pair["exponent"]]
        pair["other_packets"] = labels[pair["other_exponent"]]
    return dict(N=n, reference_p=p, reference_q=q, modulus=m,
        reference_actual_orders=orders, pairs=pairs,
        is_N_only_source=False, orders_kernel_checked=False)


def source_inventory():
    parent = json.loads((ROOT/PARENT_AUDIT).read_text())
    for path, digest in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT_AUDIT, "scripts/probe_semiprime_folded_row_coverage.py"))
    return {path:hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def main():
    from sympy import nextprime, isprime, n_order
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--bits", type=int, default=90)
    parser.add_argument("--maximum-cases", type=int, default=12)
    args = parser.parse_args()
    sources, rnd, cases = source_inventory(), random.Random(REPLAY_ID), []
    previous = json.loads((ROOT/PARENT_AUDIT).read_text())
    rare = min(previous["cases"], key=lambda c:c["folded_p_aliases"]+c["folded_q_aliases"])
    labelled = rare_pairs(rare["reference_p"], rare["reference_q"])
    print(json.dumps(dict(progress="reference-only-rare-pair-labels", **labelled)), flush=True)
    rejected = 0
    for i in range(args.maximum_cases):
        while True:
            p = int(nextprime(rnd.randrange(2**(args.bits//2-1), 2**(args.bits//2))))
            if int(n_order(2, p)) == p-1:
                break
            rejected += 1
        while True:
            q = int(nextprime(rnd.randrange(11*p//10, 19*p//10)))
            if int(n_order(2, q)) == q-1:
                break
            rejected += 1
        assert isprime(p) and isprime(q) and p <= q <= 2*p
        case = COVERAGE["reference_case"](p, q)
        cases.append(case)
        print(json.dumps(dict(progress="reference-only-wider-folded-coverage",
            sample_index=i, **case)), flush=True)
        if case["classification"] == "no-combined-alias":
            break
    assert source_inventory() == sources, "source changed during replay"
    report = dict(replay_id=REPLAY_ID, source_sha256=sources, nominal_bits=args.bits,
        maximum_reference_cases=args.maximum_cases,
        rejected_reference_prime_candidates=rejected,
        reference_condition="base 2 has full component order; reference conditioning only",
        labelled_previous_rare_case=labelled, cases=cases,
        is_N_only_source=False, is_factorization_runtime_measurement=False,
        kernel_checked_failure_control=False, is_bit_complexity_certificate=False,
        one_sixth_guarantee="OPEN",
        limitations="Private native prime/order data classify every original public packet into global inverse orbits; this does not run the public polynomial source or certify these component orders in Lean. Labelled pairs are reference diagnostics, not source advice or a universal coverage theorem. A combined reference miss would require a separate paid N-only replay before being called a public source failure. No asymptotic lower bound or exclusion of other observables follows.")
    if args.output:
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(dict(source_pins=len(sources), reference_cases=len(cases),
        found_complete_combined_reference_failure=any(c["classification"] == "no-combined-alias" for c in cases),
        one_sixth_guarantee="OPEN")), flush=True)


if __name__ == "__main__":
    main()
