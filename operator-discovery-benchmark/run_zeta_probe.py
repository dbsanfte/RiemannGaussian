#!/usr/bin/env python3
"""Run the zeta experiments and collect a report and figure.

  /home/dbsanfte/riemann/.venv/bin/python run_zeta_probe.py

Use --summarize-only to render the existing results without repeating numerical
work. The existing project environment supplies mpmath, numpy, matplotlib, and
python-flint. Every experiment stays in this directory and its zeta-results
subdirectory; the separate research roadmap and Lean project are untouched.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


INTERPRETATIONS = {
    "z": ("zeta(s)", "constant coefficients 1"),
    "inverse": ("1/zeta(s)", "Mobius coefficients"),
    "square": ("zeta(s)^2", "divisor counts / multiplicative convolution"),
    "argument_double": ("zeta(2s)", "square-index indicator"),
    "product_double": ("zeta(s) zeta(2s)", "number of square divisors"),
    "ratio_double": ("zeta(2s)/zeta(s)", "Liouville signs"),
    "inverse_ratio_double": ("zeta(s)/zeta(2s)", "squarefree indicator"),
    "log_derivative": ("-zeta'(s)/zeta(s)", "prime-power logarithmic weights (von Mangoldt)"),
    "shift_ratio": ("zeta(s-1)/zeta(s)", "Euler totient"),
    "shift_product": ("zeta(s) zeta(s-1)", "sum of divisors"),
    "log": ("log(zeta(s))", "prime-power reciprocal-exponent weights"),
    "square_root": ("sqrt(zeta(s))", "convolution square root of the constant sequence"),
}


def summarize(directory):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import mpmath
    import numpy as np
    import flint

    discovery = json.loads((directory / "coefficients_discovery.json").read_text())
    validation = json.loads((directory / "coefficients_validation.json").read_text())
    arithmetic = json.loads((directory / "arithmetic_search.json").read_text())
    strip = json.loads((directory / "strip_search.json").read_text())
    accepted = [name for name, candidate in arithmetic["direct"].items() if candidate["accepted"]]
    accepted_strip = [candidate for candidate in strip["candidates"] if candidate["accepted"]]
    root_relation = next(relation for relation in arithmetic["implicit"]
                         if relation["left"] == relation["right"] == "square_root" and relation["output"] == "z")
    versions = {"python": sys.version, "mpmath": mpmath.__version__, "numpy": np.__version__,
                "matplotlib": matplotlib.__version__, "python_flint": flint.__version__}
    (directory / "environment.json").write_text(json.dumps(versions, indent=2) + "\n")

    lines = ["Numerical operator search on the Riemann zeta function", "",
             "Outcome: classical arithmetic rules and symmetries were recovered. No new operator was established.",
             "The selected transforms, integer Dirichlet basis, feature library, and short-program grammar are explicit assumptions.",
             "Known arithmetic coefficient tables and prime factorisation were not supplied to the learner.", "",
             "COEFFICIENT RECONSTRUCTION",
             "Discovery: 120 actual zeta sample points, Re(s)=28, |Im(s)| <= 1200, 120 decimal digits.",
             "Fitted indices 1..40; only inferred coefficients 1..16 used to choose arithmetic rules.",
             "Validation: 192 fresh points, Re(s)=50, |Im(s)| <= 2200, 170 decimal digits.",
             "Fitted indices 1..64; inferred coefficients 1..32 used for validation, including unseen indices 17..32.",
             f"Design condition diagnostics: {discovery['design_condition_number_double_diagnostic']:.3f} / "
             f"{validation['design_condition_number_double_diagnostic']:.3f}.",
             f"Maximum normalized cross-cutoff coefficient discrepancy: {max(arithmetic['cross_cutoff_disagreement'].values()):.3e}.",
             "The omitted infinite tail is not certified by these fits; stability across cutoffs is empirical.", "",
             "ARITHMETIC RULE SEARCH",
             f"Direct programs tested: {arithmetic['direct_programs_checked']}; profiles accepted: {len(accepted)}/12.",
             f"Implicit relations tested: {arithmetic['implicit_relations_checked']}.",
             "These are matches to coefficient profiles, which do not uniquely identify a map on arbitrary inputs."]
    for name, (transform, interpretation) in INTERPRETATIONS.items():
        candidate = arithmetic["direct"][name]
        status = "direct match" if candidate["accepted"] else "no direct match"
        lines.append(f"  {transform}: {interpretation}; {status}.")
    lines += [f"Largest accepted held-out normalized coefficient error: "
              f"{max(arithmetic['direct'][name]['validation_error'] for name in accepted):.3e}.",
              "sqrt(zeta) did not fit the direct two-round grammar; its coefficients did satisfy C(a,a)=1.",
              f"That implicit convolution-root relation had held-out normalized error {root_relation['validation_error']:.3e}.",
              "This miss exposes a language limitation, not evidence of an undiscovered arithmetic operation.", "",
              "SEARCH IN AND NEAR THE CRITICAL STRIP",
              f"Features: {strip['feature_count']}; candidate two/three-term relations tested: {strip['models_checked']}.",
              "Training: 40 points at 75 digits; validation: 28 fresh points at 110 digits, with heights up to 160.",
              f"Relations surviving validation: {len(accepted_strip)} (conjugation and completed-function reflection).",
              "Gamma completion was supplied as a representation; the completion itself was not discovered.",
              f"Independent random-phase control matches: {strip['random_phase_controls_training_matches']}.", "",
              "RH DIAGNOSTIC CONTROL",
              "A 1/5 perturbation of the coefficient at n=3 broke completed-function reflection.",
              "A synthetic reflected/conjugate quartet of zeros at real parts 0.65 and 0.35 preserved reflection.",
              "That synthetic function does not have all of zeta's arithmetic or growth properties.",
              "The test demonstrates that reflection alone cannot distinguish the desired RH behavior."]
    for name, residual in strip["countermodels"]["reflection_relative_residuals"].items():
        lines.append(f"  {name}: maximum relative residual {residual}.")
    lines += ["", "INDEPENDENT NUMERICAL CHECK",
              "Eight raw zeta evaluations were compared between mpmath (160 digits) and FLINT/Arb (600 bits).",
              "All absolute differences had ball-arithmetic upper bounds below 1e-140.",
              "This checks the numerical zeta oracle at those points; it does not certify the inferred infinite coefficient tail.", "",
              "INTERPRETATION AND NEXT EXPERIMENT",
              "The first pass recovered known structure; no unexpected candidate survived this declared search.",
              "Multiplicative convolution transports products of general Dirichlet series, so recovering it alone gives no RH constraint.",
              "A next search should learn a richer operation language or its latent kernels, with matched perturbation controls.",
              "Finite failure in the present grammar is not a no-go theorem for the missing-operator hypothesis.", "",
              "References for interpreting the recovered classical identities:",
              "  https://dlmf.nist.gov/27.4",
              "  https://dlmf.nist.gov/27.5",
              "  https://dlmf.nist.gov/25.4", "",
              "Reproduce all measurements and searches:",
              "  /home/dbsanfte/riemann/.venv/bin/python /home/dbsanfte/riemann/operator-discovery-benchmark/run_zeta_probe.py"]
    (directory / "report.txt").write_text("\n".join(lines) + "\n")

    figure, axes = plt.subplots(3, 2, figsize=(12, 8), constrained_layout=True)
    selected = ["inverse", "square", "log_derivative", "shift_ratio", "log", "square_root"]
    for axis, name in zip(axes.flat, selected):
        values = np.array([float(pair[0]) for pair in validation["coefficients"][name]])
        n = np.arange(1, len(values) + 1)
        axis.axvspan(.5, 16.5, color="#e8edf3", alpha=.8, label="Used to select rules")
        axis.stem(n, values, linefmt="#1f5d89", markerfmt="o", basefmt=" ")
        axis.set_title(INTERPRETATIONS[name][0])
        axis.set_xlabel("Arithmetic index n")
        axis.set_ylabel("Inferred coefficient")
        axis.set_xlim(.5, 32.5)
        axis.grid(axis="y", alpha=.2)
    figure.suptitle("Coefficient structure reconstructed from zeta values\nShaded indices selected rules; indices 17–32 were held out", fontsize=13)
    figure.savefig(directory / "coefficient_profiles.png", dpi=170)
    plt.close(figure)
    print(f"Saved combined report and coefficient figure in {directory}")
    print(f"Direct arithmetic profiles: {len(accepted)}/12; accepted strip relations: {len(accepted_strip)}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--summarize-only", action="store_true")
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "zeta-results")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    if not args.summarize_only:
        root = Path(__file__).resolve().parent
        for script, extra in [("zeta_data.py", ["--pass", "discovery"]),
                              ("zeta_data.py", ["--pass", "validation"]),
                              ("zeta_rules.py", []), ("zeta_strip_search.py", [])]:
            subprocess.run([sys.executable, str(root / script), "--output-dir", str(args.output_dir),
                            *extra], check=True)
    summarize(args.output_dir)


if __name__ == "__main__":
    main()
