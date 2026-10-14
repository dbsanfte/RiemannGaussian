#!/usr/bin/env python3
"""Fresh, post-selection complete-zeta observations for the automatic winner."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import os
from pathlib import Path
import random
import flint

from compensated_shift_analytic import native_B, old_zero_disks, real, square
from compensated_shift_grammar import program_value

BASE = Path(__file__).resolve().parent


def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path): return json.loads(Path(path).read_text())
def write(path, value): Path(path).write_text(json.dumps(value, indent=2) + "\n")
def digest(value): return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family-run-dir", type=Path, required=True)
    args = parser.parse_args()
    family_directory = args.family_run_dir.resolve()
    sourcepath = family_directory / "family_gap_search.json"
    auditpath = family_directory / "family_gap_verification.json"
    source, audit = read(sourcepath), read(auditpath)
    assert audit["all_passed"] and all(audit["checks"].values())
    assert audit["source_artifact_sha256"] == sha(sourcepath)
    assert audit["checker_code_sha256"] == sha(BASE / "check_compensated_gap_family.py")
    selected = source["selected_operator"]
    assert selected is not None and selected["all_scale_bound_proved"]
    candidate = selected["candidate"]
    A = tuple((Q(w), Q(v)) for w, v in candidate["atoms"])
    destination = family_directory / "selected-native"
    destination.mkdir(exist_ok=True)
    common = {"selected_candidate": candidate, "family_search_sha256": sha(sourcepath),
              "family_verification_sha256": sha(auditpath), "producer_code_sha256": sha(Path(__file__)),
              "native_backend_code_sha256": sha(BASE / "compensated_shift_analytic.py"),
              "coefficient_backend_code_sha256": sha(BASE / "compensated_shift_grammar.py"),
              "precision": 416, "series_cap": 24, "coefficient_cutoff": 384,
              "selection_closed_before_native_cases": True,
              "evaluation_does_not_reselect_or_adapt": True,
              "comparison_gate": "overlap of complete integral and tail-enlarged coefficient enclosures; separated altered-prime control",
              "maximum_native_coordinate_radius": "1/100000000",
              "sampling": "fresh OS entropy; two rational complex points with Re(s)>4 and Re(s)>6",
              "flint_version": flint.__version__}
    protocolpath = destination / "protocol.json"
    if protocolpath.exists():
        protocol = read(protocolpath)
        assert all(protocol[k] == v for k, v in common.items()), "native protocol changed; use a fresh family run"
    else:
        seed = int.from_bytes(os.urandom(32), "big")
        generator = random.Random(seed)
        cases = [[str(Q(sigma) + Q(generator.randint(1, 15), 16)),
                  str(Q(sign * generator.randint(701, 1900), 97))]
                 for sigma, sign in ((4, 1), (6, -1))]
        protocol = {**common, "evaluation_seed": str(seed), "cases": cases}
        write(protocolpath, protocol)
    flint.ctx.prec = protocol["precision"]
    flint.ctx.cap = protocol["series_cap"]
    cutoff = protocol["coefficient_cutoff"]
    program = {"kind": "compensated_shift_program", "family": "compensated_prime_decoder",
               "left": candidate["left"], "right": candidate["right"], "input": "f"}
    B = program_value(program, {"f": [0] + [1] * cutoff})
    records = []
    for index, case in enumerate(protocol["cases"]):
        path = destination / f"producer_native_group_{index}.json"
        previous = read(path) if path.exists() else {}
        if previous.get("protocol_sha256") == digest(protocol) and previous.get("record", {}).get("all_passed"):
            records.append(previous["record"])
            print("Reused post-selection producer group", index, flush=True)
            continue
        sigma, height = map(Q, case)
        s = flint.acb(real(sigma), real(height))
        value, certificate = native_B(s, sigma, A)
        partial = sum((B[n] * (-s * flint.arb(n).log()).exp() for n in range(2, cutoff + 1)), flint.acb(0))
        # The independently certified global gap gives |B(n)|<=1 at all n>=2.
        tail = real(cutoff) ** real(1 - sigma) / real(sigma - 1)
        difference = (partial - value).abs_upper()
        wrong = (partial + real(Q(1, 11)) * (-s * flint.arb(13).log()).exp() - value).abs_lower()
        overlap = value.overlaps(partial + square(tail))
        radius_cap = real(protocol["maximum_native_coordinate_radius"])
        bounded_radius = value.real.rad() < radius_cap and value.imag.rad() < radius_cap
        if not (overlap and bounded_radius and wrong > tail):
            write(destination / f"failed_group_{index}_diagnostic.json",
                  {"s": case, "protocol_sha256": digest(protocol), "rigorous_enclosures_overlap": overlap,
                   "native_coordinate_radius_cap_passed": bool(bounded_radius), "wrong_prime_rejected": bool(wrong > tail),
                   "difference_upper_ball": difference.str(35), "coefficient_tail_ball": tail.str(35)})
            raise ArithmeticError("Post-selection enclosure/negative-control gate failed; preserve this attempt")
        row = {"s": case, "native_real_ball": value.real.str(35), "native_imag_ball": value.imag.str(35),
               "complete_native_tail_certificate": certificate, "coefficient_cutoff": cutoff,
               "coefficient_tail_ball": tail.str(35), "difference_upper_ball": difference.str(35),
               "rigorous_coefficient_series_enclosure_overlaps_native": overlap,
               "native_coordinate_radius_cap_passed": bool(bounded_radius),
               "wrong_prime": 13, "wrong_prime_difference_lower_ball": wrong.str(35), "all_passed": True}
        write(path, {"protocol_sha256": digest(protocol), "record": row})
        records.append(row)
        print("Post-selection complete native group", index, case, True, flush=True)
    result = {"all_passed": True, "protocol_sha256": digest(protocol), "selected_candidate": candidate,
              "actual_zeta_ball_checks": records, "old_actual_zero_controls": old_zero_disks(A),
              "simple_zero_signature": str(sum(w / v for w, v in A)),
              "new_RH_estimate_proved": False, "historical_novelty_established": False,
              "verified_new_operators": []}
    write(destination / "selected_analytic.json", result)
    print("Post-selection producer completed", len(records), "complete native groups", flush=True)


if __name__ == "__main__": main()
