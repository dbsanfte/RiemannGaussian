#!/usr/bin/env python3
"""Exact disk certificates for carry-filtered root correction factors.

These are sufficient zero-free bounds. A failed bound means unresolved;
it is NOT evidence that a zero exists. Historical novelty remains separate.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path

from mixed_root_search import local_fold
from root_probe import ROOT_ORDERS, local_root_coefficients


def tail_bound(order, parameter, degree, radius):
    magnitude = abs(Q(parameter))
    if magnitude <= 1:
        # Each weighted local coefficient is an average of weights with
        # magnitude <=1: the unweighted q-fold root coefficient equals 1.
        return 2 * radius ** (degree + 1) / (1 - radius), "bounded_coefficients"
    if magnitude == 2:
        power = order - 1
        # A q-way base-ell carry has at most q-1 carries per digit. Hence
        # its 2-weight is at most 2**(q-1)*(e+1)**(q-1), since ell>=2.
        ratio = radius * Q(degree + 2, degree + 1) ** power
        if ratio >= 1:
            raise ValueError("Increase degree to make the polynomial tail ratio <1")
        bound = (2 ** order * (degree + 2) ** power * radius ** (degree + 1)
                 / (1 - ratio))
        return bound, "polynomial_weight_bound"
    raise ValueError("No tail theorem supplied for this parameter")


def certificate(order, operator, local_root, radius):
    local = local_fold(local_root, order, operator)
    correction = [local[0]] + [local[e] - local[e - 1] for e in range(1, len(local))]
    degree = len(local_root) - 1
    finite = sum((abs(correction[e]) * radius ** e for e in range(2, degree + 1)), Q(0))
    tail, theorem = tail_bound(order, operator["parameter"], degree, radius)
    upper = finite + tail
    return {"root_order": order, "operator": operator, "local_degree": degree,
            "radius": str(radius), "finite_absolute_sum": str(finite),
            "tail_bound": str(tail), "total_bound": str(upper),
            "total_bound_decimal_diagnostic": float(upper),
            "tail_theorem": theorem,
            "certified_no_local_zeros_in_closed_disk": upper < 1,
            "certifies_no_correction_zeros_Re_s_gt_half": upper < 1,
            "unresolved_is_not_a_zero_counterexample": True}


def independently_verify(record):
    """Recompute the rational inequality witness, without trusting its flags."""
    radius = Q(record["radius"])
    if radius ** 2 <= Q(1, 2) or radius >= 1:
        return False
    finite, tail, total = map(Q, [record["finite_absolute_sum"], record["tail_bound"],
                                 record["total_bound"]])
    recomputed_tail, theorem = tail_bound(record["root_order"], record["operator"]["parameter"],
                                         record["local_degree"], radius)
    return (finite >= 0 and tail == recomputed_tail and theorem == record["tail_theorem"]
            and total == finite + tail and (total < 1) == record["certified_no_local_zeros_in_closed_disk"])


def main():
    destination = Path(__file__).resolve().parent / "root-results" / "carry_zero_audit.json"
    degree, radius = 48, Q(71, 100)
    records = []
    for order in ROOT_ORDERS:
        root = local_root_coefficients(order, degree)
        for prime in (2, 3, 5, 7):
            for parameter in ("0", "1/2", "2", "-1"):
                operator = {"kind": "carry", "prime": prime, "parameter": parameter}
                records.append(certificate(order, operator, root, radius))
        print(f"Audited root order {order}: {sum(x['certified_no_local_zeros_in_closed_disk'] for x in records)}/{len(records)} disk certificates passed", flush=True)
    checks = [independently_verify(record) for record in records]
    uniform = [
        {"root_order_domain": "every integer q>=2", "base_prime_domain": "every prime ell>=5",
         "parameter_domain": "every real t in [0,1]", "radius": str(radius),
         "bound": str(radius ** 5 / (1 - radius)),
         "certified_nonzero_correction_Re_s_gt_half": radius ** 5 / (1 - radius) < 1},
        {"root_order_domain": "every integer q>=2", "base_prime_domain": "every prime ell>=7",
         "parameter_domain": "every real t in [-1,1]", "radius": str(radius),
         "bound": str(2 * radius ** 7 / (1 - radius)),
         "certified_nonzero_correction_Re_s_gt_half": 2 * radius ** 7 / (1 - radius) < 1},
    ]
    result = {"proof": "carry_zero_proof.txt", "radius": str(radius), "local_degree": degree,
              "certificates": records, "all_inequality_witness_checks_passed": all(checks),
              "certified_count": sum(x["certifies_no_correction_zeros_Re_s_gt_half"] for x in records),
              "unresolved_count": sum(not x["certifies_no_correction_zeros_Re_s_gt_half"] for x in records),
              "uniform_parameter_theorems": uniform,
              "verified_new_operators": []}
    destination.write_text(json.dumps(result, indent=2) + "\n")
    assert all(checks)
    print(f"Saved {destination}", flush=True)


if __name__ == "__main__":
    main()
