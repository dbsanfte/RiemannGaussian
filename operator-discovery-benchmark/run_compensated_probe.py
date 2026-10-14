#!/usr/bin/env python3
"""Audit/publish existing signed results, or explicitly refresh their data.

Run-directory overrides affect artifact destinations only. Search rules remain
the ones pinned in compensated_gap_family_search.py and its protocol.
"""
import argparse
import importlib
import json
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent
DEST = BASE / "compensated-shift-results"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh-observations", action="store_true")
    parser.add_argument("--family-run-dir", type=Path)
    args = parser.parse_args()
    family_directory = args.family_run_dir
    if family_directory is None:
        if args.refresh_observations:
            index = 1
            while (DEST / f"family-gap-run-{index:03d}").exists():
                index += 1
            family_directory = DEST / f"family-gap-run-{index:03d}"
        elif (DEST / "latest.json").exists():
            family_directory = Path(json.loads((DEST / "latest.json").read_text())["family_run_directory"])
        else:
            family_directory = DEST / "family-gap-run-001"
    if not family_directory.is_absolute():
        family_directory = (BASE / family_directory).resolve()
    if args.refresh_observations and family_directory.exists():
        raise ValueError("Refreshed observations require a fresh frozen family run directory")
    scripts = []
    if args.refresh_observations:
        scripts += ["compensated_shift_search.py", "compensated_shift_analytic.py", "compensated_global_gap_probe.py"]
    scripts += ["check_compensated_global_gap.py", "check_compensated_shift.py", "check_compensated_shift_analytic.py"]
    for name in scripts:
        subprocess.run([sys.executable, str(BASE / name)], check=True, cwd=BASE)
    if args.refresh_observations:
        producer = importlib.import_module("compensated_gap_family_search")
        producer.DEST = family_directory
        producer.main()
    checker = importlib.import_module("check_compensated_gap_family")
    checker.DEST = family_directory
    checker.main()
    for name in ("compensated_selected_analytic.py", "check_compensated_selected_analytic.py"):
        subprocess.run([sys.executable, str(BASE / name), "--family-run-dir", str(family_directory)],
                       check=True, cwd=BASE)
    from compensated_shift_report import publish
    result = publish(family_directory)
    print("Signed family checked and published:", len(result["proved_global_estimates"]), "proved estimates")


if __name__ == "__main__":
    main()
