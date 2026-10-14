#!/usr/bin/env python3
"""Challenge the disk certificate with independently known polynomial roots.

Includes an interior zero hidden after a passing first reflection step and
a stable polynomial whose allowed infinite tail is too large to certify.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path

from schur_root_audit import schur_certificate


def main():
    cases = [
        ("constant", [Q(1)], Q(0), True, True),
        ("root_at_two", [Q(1), Q(-1, 2)], Q(1, 4), True, True),
        ("two_exterior_roots", [Q(1), Q(-5, 6), Q(1, 6)], Q(0), True, True),
        ("interior_root", [Q(1), Q(-2)], Q(0), False, False),
        # (1-3z)(1-z/5): roots 1/3 and 5. The leading coefficient 3/5
        # passes the first reflection, so the next step must catch the zero.
        ("interior_root_after_first_step", [Q(1), Q(-16, 5), Q(3, 5)], Q(0), False, False),
        ("boundary_root", [Q(1), Q(-1)], Q(0), False, False),
        # 1-z/2 is stable but adding a bounded tail of size 3/4 could
        # invalidate zero-freeness. The full-factor certificate must fail.
        ("tail_exceeds_margin", [Q(1), Q(-1, 2)], Q(3, 4), True, False),
    ]
    records = []
    for name, polynomial, tail, expected_polynomial, expected_full in cases:
        actual = schur_certificate(polynomial, Q(1), tail, precision=200)
        passed = (actual["schur_polynomial_disk_certified"] == expected_polynomial
                  and actual["full_local_disk_certified"] == expected_full)
        if name == "interior_root_after_first_step":
            passed &= actual["first_failed_degree"] == 1
        records.append({"name": name, "coefficients": [str(x) for x in polynomial],
                        "tail": str(tail), "expected_polynomial_certified": expected_polynomial,
                        "expected_full_factor_certified": expected_full,
                        "actual": actual, "passed": passed})
    result = {"records": records, "all_passed": all(x["passed"] for x in records)}
    destination = Path(__file__).resolve().parent / "root-results" / "schur_controls.json"
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Schur disk controls: {sum(x['passed'] for x in records)}/{len(records)} passed")
    assert result["all_passed"]


if __name__ == "__main__":
    main()
