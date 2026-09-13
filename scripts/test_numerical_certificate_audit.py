#!/usr/bin/env python3
"""Regression-check the final audit against a conditional replacement.

Copyright (c) 2026 David Sanftenberg. Released under Apache 2.0.
Requires the complete optional target to be built. The positive audit must
pass first, so a missing build or an unrelated Lean error cannot count as a
successful rejection test. All probe reports belong to temporary directories.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import tempfile

from numerical_certificate import ROOT, fingerprint
from verify_numerical_certificate import lake_command


def lean_string(value):
    return json.dumps(str(value), ensure_ascii=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--audit", type=Path, default=ROOT / "scripts/AuditNumericalCertificate.lean")
    parser.add_argument("--output", type=Path, default=ROOT / ".lake/numerical-certificate/audit-regression")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    marker = args.output / "result.json"
    marker.unlink(missing_ok=True)
    source = args.audit.read_text()
    expected = "\n  RiemannGaussian.Zeta23InverseSampling.simpleCritical_6731_eventually\n"
    conditional = "\n  RiemannGaussian.Zeta23InverseSampling.simpleCritical_6731_of_integer_cover\n"
    if source.count(expected) != 1:
        raise RuntimeError("The exact unconditional audit assignment was not found uniquely")
    commands, env = lake_command()
    digest = fingerprint()
    results = {}
    with tempfile.TemporaryDirectory(prefix="numerical-certificate-audit-") as directory:
        temporary = Path(directory)
        for label in ["positive", "conditional-rejected"]:
            report_dir = temporary / label
            report = report_dir / "audit.json"
            probe = source.replace('".lake/numerical-certificate"', lean_string(report_dir))
            probe = probe.replace('".lake/numerical-certificate/audit.json"', lean_string(report))
            if label == "conditional-rejected":
                probe = probe.replace(expected, conditional)
            path = temporary / (label + ".lean")
            path.write_text(probe)
            log = args.output / (label + ".log")
            with log.open("w") as stream:
                process = subprocess.run(commands + ["env", "lean", "-DwarningAsError=true", str(path)],
                                         cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
            results[label] = process.returncode
            if label == "positive":
                if process.returncode or not report.is_file():
                    raise RuntimeError(f"The genuine complete audit did not pass; see {log}")
                json.loads(report.read_text())
            else:
                messages = log.read_text()
                if (process.returncode == 0 or report.exists() or "Type mismatch" not in messages
                        or "unexpected transitive axiom" not in messages):
                    raise RuntimeError(f"The conditional replacement was not safely rejected; see {log}")
    if fingerprint() != digest:
        raise RuntimeError("Certificate inputs changed during the audit regression")
    marker.write_text(json.dumps({"state": "passed", "inputSha256": digest, "exitCodes": results,
                                 "conditionalReplacementProducesReport": False}, indent=2) + "\n")
    print("The complete audit passed; a conditional replacement was rejected without a success report.")


if __name__ == "__main__":
    main()
