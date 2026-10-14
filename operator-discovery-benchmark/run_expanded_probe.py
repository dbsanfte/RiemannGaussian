#!/usr/bin/env python3
"""Run the expanded operator detector and build a scoped proof registry."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path


BASE = Path(__file__).resolve().parent


def main():
    from detector_workflow_guard import require_verified_runtime
    require_verified_runtime()
    parser = argparse.ArgumentParser(description=__doc__)
    modes=parser.add_mutually_exclusive_group()
    modes.add_argument("--summarize-only", action="store_true")
    modes.add_argument("--signed-arithmetic-only", action="store_true",
                       help="Search typed signed arithmetic and complete scale stencils, retaining earlier stages")
    parser.add_argument("--signed-arithmetic-run-dir", type=Path,
                        help="Fresh signed arithmetic destination or an existing verified run")
    modes.add_argument("--creative-only", action="store_true",
                       help="Run creative, QRH and global-moment stages, retaining prior verified artifacts")
    modes.add_argument("--fractional-only", action="store_true",
                       help="Run fractional-prime arithmetic and analytic stages, retaining prior artifacts")
    modes.add_argument("--prime-moments-only", action="store_true",
                       help="Run global and actual-prime moment stages, retaining analytic artifacts")
    modes.add_argument("--shift-ratio-only", action="store_true",
                       help="Run unequal-shift arithmetic and complete native-zeta audits, retaining prior artifacts")
    modes.add_argument("--estimates-only", action="store_true",
                       help="Search and independently verify estimates, retaining prior operator and native-zeta artifacts")
    modes.add_argument("--autonomous-only", action="store_true",
                       help="Run a fresh frozen independent-search pilot, retaining earlier verified stages")
    modes.add_argument("--compensated-only", action="store_true",
                       help="Independently recheck and publish the signed family and global-gap certificates")
    modes.add_argument("--signed-control-only", action="store_true",
                       help="Run a fresh signed-sum operator and moment-estimate search toward RH")
    modes.add_argument("--stable-scale-only", action="store_true",
                       help="Search signed scale polynomials beyond triangle contraction, with full inverse costs")
    modes.add_argument("--mellin-only", action="store_true",
                       help="Run the primary signed search with direct RH moment targets and actual-zero obstructions")
    modes.add_argument("--signed-defects-only", action="store_true",
                       help="Infer signed moment recurrences from complete arithmetic windows")
    modes.add_argument("--fractional-powers-only", action="store_true",
                       help="Search rational roots and fractional signed moments with audited RH recovery")
    modes.add_argument("--fractional-branches-only", action="store_true",
                       help="Audit local pole and ordinary-zero obstructions for rational zeta powers")
    modes.add_argument("--signed-global-only", action="store_true",
                       help="Verify a named imported signed bound with an independent complete finite patch")
    modes.add_argument("--pole-neutral-only", action="store_true",
                       help="Search signed coefficient roots and fractional logarithmic kernels toward RH")
    modes.add_argument("--parameter-jets-only", action="store_true",
                       help="Calibrate general parameter jets and their actual-prime error identity")
    modes.add_argument("--prime-error-only", action="store_true",
                       help="Search signed prime-error filters without an all-height nonvanishing gate")
    modes.add_argument("--prime-discrepancy-only", action="store_true",
                       help="Discover universal prime-density certificates and search signed prime-error correlations")
    modes.add_argument("--prime-twists-only", action="store_true",
                       help="Search fractional prime twists and signed negative decay with charged ordinary-zeta recovery")
    modes.add_argument("--prime-oscillation-only", action="store_true",
                       help="Audit generic oscillation obstructions and evaluate sealed positive-log repairs")
    modes.add_argument("--fractional-remainders-only", action="store_true",
                       help="Search fractional discrete/continuous families with infinite-parameter ordinary-zero recovery")
    modes.add_argument("--mertens-limits-only", action="store_true",
                       help="Audit small-order inverse bounds against a named Mertens extremum and evaluate sealed log repairs")
    modes.add_argument("--mellin-kernels-only", action="store_true",
                       help="Search complete signed inverse tails and growth bounds approaching the critical exponent")
    modes.add_argument("--kernel-correlations-only", action="store_true",
                       help="Search complete signed Gram operators and centered squarefree density bounds")
    modes.add_argument("--lattice-synthesis-only", action="store_true",
                       help="Synthesize typed lattice global bounds and complementary fractional-dilation targets")
    modes.add_argument("--root-lattices-only", action="store_true",
                       help="Search normalized arithmetic roots and anonymous signed-profile proof synthesis")
    modes.add_argument("--divisor-preconditioners-only", action="store_true",
                       help="Search divisor preconditioners and logarithmic roots retaining actual signed remainders")
    modes.add_argument("--branch-centers-only", action="store_true",
                       help="Search complete fractional centers and recovering signed cofinal parameter families")
    modes.add_argument("--critical-defects-only", action="store_true",
                       help="Audit the RH signed-energy inequality, proved common-factor pieces and its dense residual")
    modes.add_argument("--divisor-duals-only", action="store_true",
                       help="Surface full-defect matrix candidates, freeze their proof queue, then attempt analytical proofs")
    modes.add_argument("--signed-gap-profiles-only", action="store_true",
                       help="Search independent exponent and constant laws against actual large-scale signed arithmetic gaps")
    modes.add_argument("--signed-gap-cofinal-only", action="store_true",
                       help="Audit cofinal parameter endpoints of existing frozen actual signed-gap candidates")
    modes.add_argument("--candidate-reviews-only", action="store_true",
                       help="Independently check completed parallel analytical reviews and publish their dispositions")
    modes.add_argument("--inverse-prefix-only", action="store_true",
                       help="Infer compressed inverse operators and search signed energy potentials")
    parser.add_argument("--inverse-prefix-run-dir", type=Path,
                        help="Fresh inverse-prefix destination or an existing completed verified run")
    parser.add_argument("--autonomous-run-dir", type=Path,
                        help="Fresh independence-stage destination; existing sealed runs are retained")
    parser.add_argument("--signed-control-run-dir", type=Path,
                        help="Fresh signed-control destination; existing sealed runs are retained")
    parser.add_argument("--stable-scale-run-dir", type=Path,
                        help="Fresh scale-polynomial destination; existing sealed runs are retained")
    parser.add_argument("--mellin-run-dir", type=Path,
                        help="Fresh primary signed-search destination; existing sealed runs are retained")
    parser.add_argument("--signed-defects-run-dir", type=Path,
                        help="Fresh signed-defect destination")
    parser.add_argument("--fractional-powers-run-dir", type=Path,
                        help="Fresh rational-power destination")
    parser.add_argument("--fractional-branches-run-dir", type=Path,
                        help="Fresh local fractional-branch audit destination")
    parser.add_argument("--signed-global-run-dir", type=Path,
                        help="Fresh imported global signed-calibration destination")
    parser.add_argument("--pole-neutral-run-dir", type=Path,
                        help="Fresh fractional coefficient-search destination")
    parser.add_argument("--pole-branch-run", type=Path,
                        help="Verified ordinary-zeta local branch audit for the coefficient search")
    parser.add_argument("--parameter-jets-run-dir", type=Path,
                        help="Fresh guided parameter-jet calibration destination")
    parser.add_argument("--parameter-source-run", type=Path,
                        help="Verified fractional coefficient-search source for the jet calibration")
    parser.add_argument("--prime-error-run-dir", type=Path,
                        help="Fresh signed prime-error search destination")
    parser.add_argument("--prime-error-source-run", type=Path,
                        help="Verified parameter-jet source for the prime-error search")
    parser.add_argument("--prime-discrepancy-run-dir", type=Path,
                        help="Fresh floor-density and signed-correlation destination")
    parser.add_argument("--prime-discrepancy-source-run", type=Path,
                        help="Verified prime-error program source for the correlation search")
    parser.add_argument("--prime-twists-run-dir", type=Path,
                        help="Fresh fractional-prime-twist destination")
    parser.add_argument("--prime-twists-source-run", type=Path,
                        help="Verified prime-density and signed-correlation source")
    parser.add_argument("--prime-oscillation-run-dir", type=Path,
                        help="Fresh oscillation-compatibility audit destination")
    parser.add_argument("--prime-oscillation-source-run", type=Path,
                        help="Verified fractional-prime-twist source")
    parser.add_argument("--prime-oscillation-coverage-run", type=Path,
                        help="Optional verified exhaustive coverage for the same source")
    parser.add_argument("--fractional-remainders-run-dir", type=Path,
                        help="Fresh fractional-remainder family destination")
    parser.add_argument("--fractional-remainders-source-run", type=Path,
                        help="Verified oscillation-compatibility source; earlier data is development")
    parser.add_argument("--mertens-limits-run-dir", type=Path,
                        help="Fresh small-order limit compatibility destination")
    parser.add_argument("--mertens-limits-source-run", type=Path,
                        help="Verified fractional-remainder family source")
    parser.add_argument("--mellin-kernels-run-dir", type=Path,
                        help="Fresh complete-tail kernel search destination")
    parser.add_argument("--mellin-kernels-source-run", type=Path,
                        help="Verified small-order Mertens compatibility source")
    parser.add_argument("--kernel-correlations-run-dir", type=Path,
                        help="Fresh signed Gram and density-search destination")
    parser.add_argument("--kernel-correlations-source-run", type=Path,
                        help="Verified complete-tail Mellin kernel source")
    parser.add_argument("--lattice-synthesis-run-dir", type=Path,
                        help="Fresh typed lattice estimate-synthesis destination")
    parser.add_argument("--lattice-synthesis-source-run", type=Path,
                        help="Verified complete signed Gram source; final outcomes are denied to discovery")
    parser.add_argument("--root-lattices-run-dir", type=Path,
                        help="Fresh normalized arithmetic-root destination")
    parser.add_argument("--root-lattices-source-run", type=Path,
                        help="Verified typed-lattice source; discovery receives coefficient patterns only")
    parser.add_argument("--divisor-preconditioners-run-dir", type=Path,
                        help="Fresh divisor-preconditioner and logarithmic-root destination")
    parser.add_argument("--divisor-preconditioners-source-run", type=Path,
                        help="Verified normalized-root source for the retained-remainder stage")
    parser.add_argument("--branch-centers-run-dir", type=Path,
                        help="Fresh complete fractional-center and cofinal signed-family destination")
    parser.add_argument("--branch-centers-source-run", type=Path,
                        help="Verified retained-arithmetic source; final outcomes remain private to evaluation")
    parser.add_argument("--critical-defects-run-dir", type=Path,
                        help="Fresh critical signed-defect audit destination")
    parser.add_argument("--critical-defects-source-run", type=Path,
                        help="Verified fractional-center source; the target audit keeps prior outcomes private")
    parser.add_argument("--divisor-duals-run-dir", type=Path,
                        help="Fresh full-defect detector and separate analytical-review destination")
    parser.add_argument("--divisor-duals-source-run", type=Path,
                        help="Verified full signed-energy-defect source; discovery cannot read prior outcomes")
    parser.add_argument("--signed-gap-profiles-run-dir", type=Path,
                        help="Fresh independent-constant signed-gap search and analytical-review destination")
    parser.add_argument("--signed-gap-profiles-source-run", type=Path,
                        help="Verified divisor-dual source with a separate completed analytical review")
    parser.add_argument("--signed-gap-cofinal-audit-dir", type=Path,
                        help="Fresh analytical cofinal audit destination; original runs remain unchanged")
    parser.add_argument("--signed-gap-cofinal-source-run", type=Path,
                        help="Existing verified signed-gap profile run whose formulas will be audited")
    parser.add_argument("--candidate-review-round-dir", type=Path,
                        help="Prepared round containing frozen assignments and completed Sol 6.1 reviews")
    parser.add_argument("--signed-source-run", type=Path,
                        help="Verified primary signed-search source for the defect and fractional stages")
    parser.add_argument("--max-root-denominator", type=int, default=12,
                        help="Rational-power pilot budget; the grammar has no semantic denominator ceiling")
    args = parser.parse_args()
    if args.signed_arithmetic_only:
        from signed_arithmetic_search import run as run_signed_arithmetic
        from signed_arithmetic_report import summary as summarize_signed_arithmetic
        destination = args.signed_arithmetic_run_dir
        if destination is None:
            raise ValueError("--signed-arithmetic-only requires --signed-arithmetic-run-dir")
        if destination.exists():
            summarize_signed_arithmetic(destination)
        else:
            run_signed_arithmetic(destination)
        # This mode dispatches only the new stage; publication strict-loads
        # historical artifacts without rerunning their producers.
        args.summarize_only = True
    if not args.summarize_only:
        scripts=("root_probe.py", "mixed_root_search.py", "carry_zero_audit.py",
                     "check_carry_certificates.py", "schur_root_audit.py", "check_schur_controls.py",
                     "shift_grammar_search.py", "root_transfer_probe.py", "check_root_transfer.py",
                     "transfer_analytic_probe.py", "global_carry_probe.py", "global_analytic_probe.py",
                     "dyadic_root_search.py", "check_dyadic_roots.py", "dyadic_analytic_probe.py",
                     "projection_search.py", "check_projection.py", "projection_analytic_probe.py",
                     "check_projection_analytic.py", "coupling_search.py", "check_coupling.py",
                     "coupling_analytic_probe.py", "check_coupling_analytic.py",
                     "size_carry_search.py", "check_size_carry.py",
                     "size_analytic_probe.py", "check_size_analytic.py",
                     "size_resonance_probe.py", "check_size_resonance.py",
                     "joint_size_search.py", "check_joint_size.py",
                     "joint_size_analytic.py", "check_joint_size_analytic.py",
                     "cancellation_search.py", "check_cancellation.py",
                     "cancellation_analytic.py", "check_cancellation_analytic.py",
                     "mixed_index_search.py", "check_mixed_index.py",
                     "mixed_index_analytic.py", "check_mixed_index_analytic.py",
                     "difference_search.py", "check_difference.py",
                     "difference_analytic.py", "check_difference_analytic.py",
                     "pair_search.py", "check_pair.py",
                     "pair_analytic.py", "check_pair_analytic.py",
                     "pair_fibre_probe.py", "decode_search.py", "check_decode.py",
                     "decode_analytic.py", "check_decode_analytic.py",
                     "prime_pair_search.py", "check_prime_pair.py",
                     "prime_pair_analytic.py", "check_prime_pair_analytic.py",
                     "visible_search.py", "check_visible.py",
                     "visible_analytic.py", "check_visible_analytic.py",
                     "gap_endpoint_probe.py", "gap_search.py", "check_gap.py",
                     "gap_analytic.py", "check_gap_analytic.py",
                     "laplacian_search.py", "check_laplacian.py",
                     "laplacian_analytic.py", "check_laplacian_analytic.py",
                     "moment_search.py", "check_moment.py",
                     "moment_analytic.py", "check_moment_analytic.py",
                     "radix_search.py", "check_radix.py",
                     "radix_analytic.py", "check_radix_analytic.py",
                     "prime_scale_search.py", "check_prime_scale.py",
                     "prime_scale_analytic.py", "check_prime_scale_analytic.py",
                     "qrh_operator_benchmark.py", "check_qrh_operators.py",
                     "creative_search.py", "check_creative_grammar.py",
                     "global_moment_search.py", "check_global_moments.py")
        scripts += ("fractional_prime_search.py", "check_fractional_prime.py",
                    "fractional_prime_analytic.py", "check_fractional_prime_analytic.py",
                    "prime_moment_transfer.py", "check_prime_moment_transfer.py",
                    "shift_ratio_search.py", "check_shift_ratio.py",
                    "shift_ratio_analytic.py", "check_shift_ratio_analytic.py",
                    "estimate_search.py", "check_estimates.py", "plot_estimates.py",
                    "cancellation_rewrite_search.py", "check_cancellation_rewrites.py")
        if args.creative_only:
            scripts=("qrh_operator_benchmark.py", "check_qrh_operators.py",
                     "creative_search.py", "check_creative_grammar.py",
                     "global_moment_search.py", "check_global_moments.py")
        if args.fractional_only:
            scripts=("fractional_prime_search.py", "check_fractional_prime.py",
                     "fractional_prime_analytic.py", "check_fractional_prime_analytic.py",
                     "prime_moment_transfer.py", "check_prime_moment_transfer.py")
        if args.prime_moments_only:
            scripts=("global_moment_search.py", "check_global_moments.py",
                     "prime_moment_transfer.py", "check_prime_moment_transfer.py")
        if args.shift_ratio_only:
            scripts=("shift_ratio_search.py", "check_shift_ratio.py",
                     "shift_ratio_analytic.py", "check_shift_ratio_analytic.py",
                     "estimate_search.py", "check_estimates.py", "plot_estimates.py",
                     "cancellation_rewrite_search.py", "check_cancellation_rewrites.py")
        if args.estimates_only:
            scripts=("estimate_search.py", "check_estimates.py", "plot_estimates.py",
                     "cancellation_rewrite_search.py", "check_cancellation_rewrites.py")
        if args.autonomous_only:
            scripts=()
        if args.compensated_only:
            scripts=("run_compensated_probe.py",)
        if args.signed_control_only:
            scripts=()
        if args.stable_scale_only:
            scripts=()
        if args.mellin_only:
            scripts=()
        if (args.signed_defects_only or args.fractional_powers_only or args.fractional_branches_only
                or args.signed_global_only or args.pole_neutral_only or args.parameter_jets_only
                or args.prime_error_only or args.prime_discrepancy_only or args.prime_twists_only
                or args.prime_oscillation_only or args.fractional_remainders_only or args.mertens_limits_only
                or args.mellin_kernels_only or args.kernel_correlations_only or args.lattice_synthesis_only
                or args.root_lattices_only or args.divisor_preconditioners_only or args.branch_centers_only
                or args.critical_defects_only or args.divisor_duals_only or args.signed_gap_profiles_only or args.signed_gap_cofinal_only or args.candidate_reviews_only or args.inverse_prefix_only):
            scripts=()
        for name in scripts:
            subprocess.run([sys.executable, str(BASE / name)], check=True, cwd=BASE)
        full_run = not any((args.creative_only, args.fractional_only, args.prime_moments_only,
                            args.shift_ratio_only, args.estimates_only, args.autonomous_only,
                            args.compensated_only, args.signed_control_only, args.stable_scale_only,
                            args.mellin_only, args.signed_defects_only, args.fractional_powers_only,
                            args.fractional_branches_only, args.signed_global_only, args.pole_neutral_only,
                            args.parameter_jets_only, args.prime_error_only, args.prime_discrepancy_only,
                            args.prime_twists_only, args.prime_oscillation_only, args.fractional_remainders_only,
                            args.mertens_limits_only,args.mellin_kernels_only,args.kernel_correlations_only,args.lattice_synthesis_only,
                            args.root_lattices_only,args.divisor_preconditioners_only,args.branch_centers_only,args.critical_defects_only,args.divisor_duals_only,args.signed_gap_profiles_only,args.signed_gap_cofinal_only,args.candidate_reviews_only,args.inverse_prefix_only))
        if full_run:
            subprocess.run([sys.executable, str(BASE / "run_compensated_probe.py"),
                            "--refresh-observations"], check=True, cwd=BASE)
        if args.signed_control_only or full_run:
            destination = args.signed_control_run_dir
            if destination is None:
                i = 1
                while (BASE / f"signed-control-results/run-{i:03d}").exists():
                    i += 1
                destination = BASE / f"signed-control-results/run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            subprocess.run([sys.executable, str(BASE / "signed_control_search.py"), "run",
                            "--run-dir", str(destination)], check=True, cwd=BASE)
        if args.stable_scale_only or full_run:
            destination = args.stable_scale_run_dir
            if destination is None:
                i = 1
                while (BASE / f"stable-scale-results/run-{i:03d}").exists():
                    i += 1
                destination = BASE / f"stable-scale-results/run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            subprocess.run([sys.executable, str(BASE / "stable_scale_search.py"), "run",
                            "--run-dir", str(destination)], check=True, cwd=BASE)
        if args.mellin_only or full_run:
            destination = args.mellin_run_dir
            if destination is None:
                i = 1
                while (BASE / f"mellin-search-results/run-{i:03d}").exists():
                    i += 1
                destination = BASE / f"mellin-search-results/run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            subprocess.run([sys.executable, str(BASE / "mellin_search.py"), "run",
                            "--run-dir", str(destination)], check=True, cwd=BASE)
        for enabled, dirname, runner, chosen in (
            (args.signed_defects_only or full_run, "signed-defect-results", "signed_defect_search.py", args.signed_defects_run_dir),
            (args.fractional_powers_only or full_run, "fractional-moment-results", "fractional_moment_search.py", args.fractional_powers_run_dir),
        ):
            if not enabled:
                continue
            source = args.signed_source_run
            if source is None:
                from mellin_search_report import load_latest as load_source
                previous = load_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified primary signed-search source is required")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE / source).resolve()
            destination = chosen
            if destination is None:
                i = 1
                while (BASE / dirname / f"run-{i:03d}").exists():
                    i += 1
                destination = BASE / dirname / f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            command = [sys.executable, str(BASE / runner), "run", "--run-dir", str(destination),
                       "--source-run", str(source)]
            if runner == "fractional_moment_search.py":
                command.extend(("--max-denominator", str(args.max_root_denominator)))
            subprocess.run(command, check=True, cwd=BASE)
        if args.fractional_powers_only or args.fractional_branches_only or full_run:
            from fractional_moment_report import load_latest as load_fractional_source
            previous = load_fractional_source()
            if previous["status"] == "not_run":
                raise ValueError("A verified fractional-power source is required for the local branch audit")
            destination = args.fractional_branches_run_dir
            if destination is None:
                i = 1
                while (BASE / "fractional-branch-results" / f"audit-{i:03d}").exists():
                    i += 1
                destination = BASE / "fractional-branch-results" / f"audit-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            subprocess.run([sys.executable, str(BASE / "fractional_zeta_branch_audit.py"),
                            "--run-dir", str(destination), "--source-run", previous["run_directory"]],
                           check=True, cwd=BASE)
        for enabled, dirname, runner, chosen in (
            (args.signed_global_only or full_run, "signed-global-results", "signed_global_calibration.py", args.signed_global_run_dir),
            (args.pole_neutral_only or full_run, "pole-neutral-results", "pole_neutral_search.py", args.pole_neutral_run_dir),
        ):
            if not enabled:
                continue
            source = args.signed_source_run
            if source is None:
                from mellin_search_report import load_latest as load_source
                previous = load_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified primary signed-search source is required")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE / source).resolve()
            destination = chosen
            if destination is None:
                i = 1
                while (BASE / dirname / f"run-{i:03d}").exists():
                    i += 1
                destination = BASE / dirname / f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            command = [sys.executable, str(BASE / runner)]
            if runner == "pole_neutral_search.py":
                branch = args.pole_branch_run
                if branch is None:
                    from fractional_zeta_branch_audit import load_latest as load_branch
                    branch_source = load_branch()
                    if branch_source["status"] == "not_run":
                        raise ValueError("A verified fractional-zeta branch audit is required")
                    branch = Path(branch_source["run_directory"])
                elif not branch.is_absolute():
                    branch = (BASE / branch).resolve()
                command.extend(("run", "--branch-run", str(branch)))
            command.extend(("--run-dir", str(destination), "--source-run", str(source)))
            subprocess.run(command, check=True, cwd=BASE)
        if args.parameter_jets_only or full_run:
            source = args.parameter_source_run
            if source is None:
                from pole_neutral_report import load_latest as load_parameter_source
                previous = load_parameter_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified fractional coefficient search is required for the jet calibration")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.parameter_jets_run_dir
            if destination is None:
                i = 1
                while (BASE/"parameter-jet-results"/f"calibration-{i:03d}").exists():
                    i += 1
                destination = BASE/"parameter-jet-results"/f"calibration-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable, str(BASE/"parameter_jet_audit.py"),
                            "--run-dir", str(destination), "--source-run", str(source)],
                           check=True, cwd=BASE)
        if args.prime_error_only or full_run:
            source = args.prime_error_source_run
            if source is None:
                from parameter_jet_report import load_latest as load_prime_error_source
                previous = load_prime_error_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified parameter-jet source is required for the prime-error search")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.prime_error_run_dir
            if destination is None:
                i = 1
                while (BASE/"prime-error-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"prime-error-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable, str(BASE/"prime_error_search.py"), "run",
                            "--run-dir", str(destination), "--source-run", str(source)],
                           check=True, cwd=BASE)
        if args.prime_discrepancy_only or full_run:
            source = args.prime_discrepancy_source_run
            if source is None:
                from prime_error_report import load_latest as load_discrepancy_source
                previous = load_discrepancy_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified prime-error source is required for the correlation search")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.prime_discrepancy_run_dir
            if destination is None:
                i = 1
                while (BASE/"prime-discrepancy-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"prime-discrepancy-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable, str(BASE/"prime_discrepancy_search.py"), "run",
                            "--run-dir", str(destination), "--source-run", str(source)],
                           check=True, cwd=BASE)
        if args.prime_twists_only or full_run:
            source = args.prime_twists_source_run
            if source is None:
                from prime_discrepancy_report import load_latest as load_twist_source
                previous = load_twist_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified prime-density source is required for the fractional-twist search")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.prime_twists_run_dir
            if destination is None:
                i = 1
                while (BASE/"prime-twist-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"prime-twist-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable, str(BASE/"prime_twist_search.py"), "run",
                            "--run-dir", str(destination), "--source-run", str(source)],
                           check=True, cwd=BASE)
        if args.prime_oscillation_only or full_run:
            source = args.prime_oscillation_source_run
            if source is None:
                from prime_twist_report import load_latest as load_oscillation_source
                previous = load_oscillation_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified fractional-twist source is required for the oscillation audit")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            coverage = args.prime_oscillation_coverage_run
            if coverage is None:
                from prime_twist_coverage_report import load_latest as load_coverage_source
                previous = load_coverage_source()
                if previous["status"] != "not_run" and Path(previous["source_run"]) == source:
                    coverage = Path(previous["run_directory"])
            elif not coverage.is_absolute():
                coverage = (BASE/coverage).resolve()
            destination = args.prime_oscillation_run_dir
            if destination is None:
                i = 1
                while (BASE/"prime-oscillation-results"/f"audit-{i:03d}").exists():
                    i += 1
                destination = BASE/"prime-oscillation-results"/f"audit-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            command = [sys.executable, str(BASE/"prime_oscillation_audit.py"), "run",
                       "--run-dir", str(destination), "--source-run", str(source)]
            if coverage is not None:
                command.extend(["--coverage-run",str(coverage)])
            subprocess.run(command,check=True,cwd=BASE)
        if args.fractional_remainders_only or full_run:
            source = args.fractional_remainders_source_run
            if source is None:
                from prime_oscillation_report import load_latest as load_remainder_source
                previous = load_remainder_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified oscillation audit is required for the fractional-remainder search")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.fractional_remainders_run_dir
            if destination is None:
                i = 1
                while (BASE/"fractional-remainder-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"fractional-remainder-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"fractional_remainder_search.py"),
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
        if args.mertens_limits_only or args.fractional_remainders_only or full_run:
            source = args.mertens_limits_source_run
            if source is None:
                from fractional_remainder_report import load_latest as load_limit_source
                previous = load_limit_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified fractional-remainder source is required for the small-order audit")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.mertens_limits_run_dir
            if destination is None:
                i = 1
                while (BASE/"mertens-limit-results"/f"audit-{i:03d}").exists():
                    i += 1
                destination = BASE/"mertens-limit-results"/f"audit-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"mertens_limit_audit.py"),
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
        if args.mellin_kernels_only or full_run:
            source = args.mellin_kernels_source_run
            if source is None:
                from mertens_limit_report import load_latest as load_kernel_source
                previous = load_kernel_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified Mertens compatibility source is required for the kernel search")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.mellin_kernels_run_dir
            if destination is None:
                i = 1
                while (BASE/"mellin-kernel-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"mellin-kernel-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"mellin_kernel_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"mellin_kernel_observer_audit.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_mellin_kernels.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.kernel_correlations_only or full_run:
            source = args.kernel_correlations_source_run
            if source is None:
                from mellin_kernel_report import load_latest as load_correlation_source
                previous = load_correlation_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified complete-tail Mellin source is required for the correlation search")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.kernel_correlations_run_dir
            if destination is None:
                i = 1
                while (BASE/"kernel-correlation-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"kernel-correlation-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"kernel_correlation_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_kernel_correlations.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.lattice_synthesis_only or full_run:
            source = args.lattice_synthesis_source_run
            if source is None:
                from kernel_correlation_report import load_latest as load_lattice_source
                previous = load_lattice_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified complete signed Gram source is required for lattice synthesis")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.lattice_synthesis_run_dir
            if destination is None:
                i = 1
                while (BASE/"lattice-synthesis-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"lattice-synthesis-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"lattice_synthesis_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"lattice_fractional_root_audit.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_lattice_synthesis.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.root_lattices_only or full_run:
            source = args.root_lattices_source_run
            if source is None:
                from lattice_synthesis_report import load_latest as load_root_source
                previous = load_root_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified typed-lattice source is required for arithmetic-root synthesis")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.root_lattices_run_dir
            if destination is None:
                i = 1
                while (BASE/"root-lattice-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"root-lattice-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"root_lattice_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_root_lattices.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.divisor_preconditioners_only or full_run:
            source = args.divisor_preconditioners_source_run
            if source is None:
                from root_lattice_report import load_latest as load_divisor_source
                previous = load_divisor_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified normalized-root source is required for divisor preconditioning")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.divisor_preconditioners_run_dir
            if destination is None:
                i = 1
                while (BASE/"divisor-preconditioner-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"divisor-preconditioner-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"divisor_preconditioner_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_divisor_preconditioners.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.branch_centers_only or full_run:
            source = args.branch_centers_source_run
            if source is None:
                from divisor_preconditioner_report import load_latest as load_branch_source
                previous = load_branch_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified retained-arithmetic source is required for fractional centers")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.branch_centers_run_dir
            if destination is None:
                i = 1
                while (BASE/"branch-center-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"branch-center-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"branch_center_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_branch_centers.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.critical_defects_only or full_run:
            source = args.critical_defects_source_run
            if source is None:
                from branch_center_report import load_latest as load_defect_source
                previous = load_defect_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified fractional-center source is required for the critical defect audit")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.critical_defects_run_dir
            if destination is None:
                i = 1
                while (BASE/"critical-defect-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"critical-defect-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"critical_defect_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_critical_defects.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.divisor_duals_only or full_run:
            source = args.divisor_duals_source_run
            if source is None:
                from critical_defect_report import load_latest as load_dual_source
                previous = load_dual_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified signed-energy-defect source is required for divisor duals")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.divisor_duals_run_dir
            if destination is None:
                i = 1
                while (BASE/"divisor-dual-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"divisor-dual-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"divisor_dual_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"divisor_dual_analytic_review.py"),
                            "--source",str(destination),"--review-dir",str(destination/"analytical-review-001")],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_divisor_dual.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
        if args.signed_gap_profiles_only or full_run:
            source = args.signed_gap_profiles_source_run
            if source is None:
                from divisor_dual_report import load_latest as load_gap_source
                previous = load_gap_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified detector-to-proof source is required for signed-gap profiles")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.signed_gap_profiles_run_dir
            if destination is None:
                i = 1
                while (BASE/"signed-gap-profile-results"/f"run-{i:03d}").exists():
                    i += 1
                destination = BASE/"signed-gap-profile-results"/f"run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"signed_gap_profile_search.py"),"run",
                            "--run-dir",str(destination),"--source",str(source)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"plot_signed_gap_profiles.py"),
                            "--run-dir",str(destination)],check=True,cwd=BASE)
            subprocess.run([sys.executable,str(BASE/"signed_gap_cofinal_audit.py"),
                            "--source",str(destination),"--audit-dir",str(destination/"cofinal-audit-001")],check=True,cwd=BASE)
        if args.signed_gap_cofinal_only:
            source = args.signed_gap_cofinal_source_run
            if source is None:
                from signed_gap_profile_report import load_latest as load_cofinal_source
                previous = load_cofinal_source()
                if previous["status"] == "not_run":
                    raise ValueError("A verified signed-gap profile source is required")
                source = Path(previous["run_directory"])
            elif not source.is_absolute():
                source = (BASE/source).resolve()
            destination = args.signed_gap_cofinal_audit_dir
            if destination is None:
                i = 1
                while (source/f"cofinal-audit-{i:03d}").exists():
                    i += 1
                destination = source/f"cofinal-audit-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE/destination).resolve()
            subprocess.run([sys.executable,str(BASE/"signed_gap_cofinal_audit.py"),
                            "--source",str(source),"--audit-dir",str(destination)],check=True,cwd=BASE)
        if args.candidate_reviews_only:
            destination = args.candidate_review_round_dir
            if destination is None:
                raise ValueError("Supply --candidate-review-round-dir after completing the prepared agent assignments")
            destination = destination.resolve() if destination.is_absolute() else (BASE/destination).resolve()
            if not (destination/"review_protocol.json").exists():
                subprocess.run([sys.executable,str(BASE/"candidate_review_workflow.py"),"finalize",
                                "--round-dir",str(destination)],check=True,cwd=BASE)
            else:
                from candidate_review_report import summary as completed_review_summary
                completed_review_summary(destination)
                (BASE/"candidate-review-results/latest.json").write_text(
                    json.dumps({"round_directory":str(destination)},indent=2)+"\n")
        if args.inverse_prefix_only or full_run:
            destination = args.inverse_prefix_run_dir
            if destination is None:
                i = 1
                while (BASE / f"inverse-prefix-results/pilot-{i:03d}").exists():
                    i += 1
                destination = BASE / f"inverse-prefix-results/pilot-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            if destination.exists():
                from inverse_prefix_report import summary as inverse_summary
                inverse_summary(destination)
                (BASE / "inverse-prefix-results/latest.json").write_text(
                    json.dumps({"run_directory": str(destination)}, indent=2) + "\n")
            else:
                subprocess.run([sys.executable, str(BASE / "inverse_prefix_search.py"), "run",
                                "--run-dir", str(destination)], check=True, cwd=BASE)
        if args.autonomous_only or not any((args.creative_only, args.fractional_only,
                                           args.prime_moments_only, args.shift_ratio_only,
                                           args.estimates_only, args.compensated_only, args.signed_control_only,
                                           args.stable_scale_only, args.mellin_only,
                                           args.signed_defects_only, args.fractional_powers_only,
                                           args.fractional_branches_only, args.signed_global_only,
                                           args.pole_neutral_only, args.parameter_jets_only,
                                           args.prime_error_only, args.prime_discrepancy_only,
                                           args.prime_twists_only, args.prime_oscillation_only,
                                           args.fractional_remainders_only,args.mertens_limits_only,
                                           args.mellin_kernels_only,args.kernel_correlations_only,args.lattice_synthesis_only,
                                           args.root_lattices_only,args.divisor_preconditioners_only,args.branch_centers_only,args.critical_defects_only,args.divisor_duals_only,args.signed_gap_profiles_only,args.signed_gap_cofinal_only,args.candidate_reviews_only,args.inverse_prefix_only)):
            destination = args.autonomous_run_dir
            if destination is None:
                i = 1
                while (BASE / f"autonomous-results/run-{i:03d}").exists():
                    i += 1
                destination = BASE / f"autonomous-results/run-{i:03d}"
            elif not destination.is_absolute():
                destination = (BASE / destination).resolve()
            subprocess.run([sys.executable, str(BASE / "autonomous_search.py"), "run",
                            "--output-dir", str(destination)], check=True, cwd=BASE)
            from autonomous_report import publish
            publish(destination)
    output_dir = BASE / "root-results"
    root = json.loads((output_dir / "root_probe.json").read_text())
    mixed = json.loads((output_dir / "mixed_root_search.json").read_text())
    carry = json.loads((output_dir / "carry_zero_audit.json").read_text())
    carry_verification = json.loads((output_dir / "carry_certificate_verification.json").read_text())
    schur = json.loads((output_dir / "schur_root_audit.json").read_text())
    schur_controls = json.loads((output_dir / "schur_controls.json").read_text())
    shift = json.loads((BASE / "shift-results/shift_search.json").read_text())
    transfer = json.loads((BASE / "transfer-results/root_transfer_probe.json").read_text())
    transfer_check = json.loads((BASE / "transfer-results/root_transfer_verification.json").read_text())
    transfer_analytic = json.loads((BASE / "transfer-results/transfer_analytic_probe.json").read_text())
    global_ = json.loads((BASE / "global-results/global_carry_probe.json").read_text())
    global_analytic = json.loads((BASE / "global-results/global_analytic_probe.json").read_text())
    dyadic = json.loads((BASE / "dyadic-results/dyadic_root_search.json").read_text())
    dyadic_check = json.loads((BASE / "dyadic-results/dyadic_root_verification.json").read_text())
    dyadic_analytic = json.loads((BASE / "dyadic-results/dyadic_analytic_probe.json").read_text())
    projection = json.loads((BASE / "projection-results/projection_search.json").read_text())
    projection_check = json.loads((BASE / "projection-results/projection_verification.json").read_text())
    projection_analytic = json.loads((BASE / "projection-results/projection_analytic_probe.json").read_text())
    projection_analytic_check = json.loads((BASE / "projection-results/projection_analytic_verification.json").read_text())
    coupling = json.loads((BASE / "coupling-results/coupling_search.json").read_text())
    coupling_check = json.loads((BASE / "coupling-results/coupling_verification.json").read_text())
    coupling_analytic = json.loads((BASE / "coupling-results/coupling_analytic_probe.json").read_text())
    coupling_analytic_check = json.loads((BASE / "coupling-results/coupling_analytic_verification.json").read_text())
    size = json.loads((BASE / "size-results/size_carry_search.json").read_text())
    size_check = json.loads((BASE / "size-results/size_carry_verification.json").read_text())
    size_analytic = json.loads((BASE / "size-results/size_analytic_probe.json").read_text())
    size_analytic_check = json.loads((BASE / "size-results/size_analytic_verification.json").read_text())
    size_resonance = json.loads((BASE / "size-results/size_resonance_probe.json").read_text())
    size_resonance_check = json.loads((BASE / "size-results/size_resonance_verification.json").read_text())
    joint = json.loads((BASE / "joint-results/joint_size_search.json").read_text())
    joint_check = json.loads((BASE / "joint-results/joint_size_verification.json").read_text())
    joint_analytic = json.loads((BASE / "joint-results/joint_size_analytic.json").read_text())
    joint_analytic_check = json.loads((BASE / "joint-results/joint_size_analytic_verification.json").read_text())
    cancellation = json.loads((BASE / "cancellation-results/cancellation_search.json").read_text())
    cancellation_check = json.loads((BASE / "cancellation-results/cancellation_verification.json").read_text())
    cancellation_analytic = json.loads((BASE / "cancellation-results/cancellation_analytic.json").read_text())
    cancellation_analytic_check = json.loads((BASE / "cancellation-results/cancellation_analytic_verification.json").read_text())
    mixed_index = json.loads((BASE / "mixed-index-results/mixed_index_search.json").read_text())
    mixed_index_check = json.loads((BASE / "mixed-index-results/mixed_index_verification.json").read_text())
    mixed_index_analytic = json.loads((BASE / "mixed-index-results/mixed_index_analytic.json").read_text())
    mixed_index_analytic_check = json.loads((BASE / "mixed-index-results/mixed_index_analytic_verification.json").read_text())
    difference = json.loads((BASE / "difference-results/difference_search.json").read_text())
    difference_check = json.loads((BASE / "difference-results/difference_verification.json").read_text())
    difference_analytic = json.loads((BASE / "difference-results/difference_analytic.json").read_text())
    difference_analytic_check = json.loads((BASE / "difference-results/difference_analytic_verification.json").read_text())
    pair = json.loads((BASE / "pair-results/pair_search.json").read_text())
    pair_check = json.loads((BASE / "pair-results/pair_verification.json").read_text())
    pair_analytic = json.loads((BASE / "pair-results/pair_analytic.json").read_text())
    pair_analytic_check = json.loads((BASE / "pair-results/pair_analytic_verification.json").read_text())
    fibres = json.loads((BASE / "decode-results/pair_fibre_probe.json").read_text())
    decode = json.loads((BASE / "decode-results/decode_search.json").read_text())
    decode_check = json.loads((BASE / "decode-results/decode_verification.json").read_text())
    decode_analytic = json.loads((BASE / "decode-results/decode_analytic.json").read_text())
    decode_analytic_check = json.loads((BASE / "decode-results/decode_analytic_verification.json").read_text())
    prime_pair = json.loads((BASE / "prime-pair-results/prime_pair_search.json").read_text())
    prime_pair_check = json.loads((BASE / "prime-pair-results/prime_pair_verification.json").read_text())
    prime_pair_analytic = json.loads((BASE / "prime-pair-results/prime_pair_analytic.json").read_text())
    prime_pair_analytic_check = json.loads((BASE / "prime-pair-results/prime_pair_analytic_verification.json").read_text())
    visible = json.loads((BASE / "visible-results/visible_search.json").read_text())
    visible_check = json.loads((BASE / "visible-results/visible_verification.json").read_text())
    visible_analytic = json.loads((BASE / "visible-results/visible_analytic.json").read_text())
    visible_analytic_check = json.loads((BASE / "visible-results/visible_analytic_verification.json").read_text())
    gap_probe = json.loads((BASE / "gap-results/gap_endpoint_probe.json").read_text())
    gap = json.loads((BASE / "gap-results/gap_search.json").read_text())
    gap_check = json.loads((BASE / "gap-results/gap_verification.json").read_text())
    gap_analytic = json.loads((BASE / "gap-results/gap_analytic.json").read_text())
    gap_analytic_check = json.loads((BASE / "gap-results/gap_analytic_verification.json").read_text())
    laplacian = json.loads((BASE / "laplacian-results/laplacian_search.json").read_text())
    laplacian_check = json.loads((BASE / "laplacian-results/laplacian_verification.json").read_text())
    laplacian_analytic = json.loads((BASE / "laplacian-results/laplacian_analytic.json").read_text())
    laplacian_analytic_check = json.loads((BASE / "laplacian-results/laplacian_analytic_verification.json").read_text())
    moment = json.loads((BASE / "moment-results/moment_search.json").read_text())
    moment_check = json.loads((BASE / "moment-results/moment_verification.json").read_text())
    moment_analytic = json.loads((BASE / "moment-results/moment_analytic.json").read_text())
    moment_analytic_check = json.loads((BASE / "moment-results/moment_analytic_verification.json").read_text())
    radix = json.loads((BASE / "radix-results/radix_search.json").read_text())
    radix_check = json.loads((BASE / "radix-results/radix_verification.json").read_text())
    radix_analytic = json.loads((BASE / "radix-results/radix_analytic.json").read_text())
    radix_analytic_check = json.loads((BASE / "radix-results/radix_analytic_verification.json").read_text())
    prime_scale = json.loads((BASE / "prime-scale-results/prime_scale_search.json").read_text())
    prime_scale_check = json.loads((BASE / "prime-scale-results/prime_scale_verification.json").read_text())
    prime_scale_analytic = json.loads((BASE / "prime-scale-results/prime_scale_analytic.json").read_text())
    prime_scale_analytic_check = json.loads((BASE / "prime-scale-results/prime_scale_analytic_verification.json").read_text())
    qrh = json.loads((BASE / "qrh-results/qrh_operator_benchmark.json").read_text())
    qrh_check = json.loads((BASE / "qrh-results/qrh_operator_verification.json").read_text())
    creative = json.loads((BASE / "creative-results/creative_search.json").read_text())
    creative_check = json.loads((BASE / "creative-results/creative_verification.json").read_text())
    global_moment = json.loads((BASE / "global-moment-results/global_moment_search.json").read_text())
    global_moment_check = json.loads((BASE / "global-moment-results/global_moment_verification.json").read_text())
    fractional = json.loads((BASE / "fractional-prime-results/fractional_prime_search.json").read_text())
    fractional_check = json.loads((BASE / "fractional-prime-results/fractional_prime_verification.json").read_text())
    fractional_analytic = json.loads((BASE / "fractional-prime-results/fractional_prime_analytic.json").read_text())
    fractional_analytic_check = json.loads((BASE / "fractional-prime-results/fractional_prime_analytic_verification.json").read_text())
    prime_moment = json.loads((BASE / "prime-moment-results/prime_moment_transfer.json").read_text())
    prime_moment_check = json.loads((BASE / "prime-moment-results/prime_moment_verification.json").read_text())
    shift_ratio = json.loads((BASE / "shift-ratio-results/shift_ratio_search.json").read_text())
    shift_ratio_check = json.loads((BASE / "shift-ratio-results/shift_ratio_verification.json").read_text())
    shift_ratio_analytic = json.loads((BASE / "shift-ratio-results/shift_ratio_analytic.json").read_text())
    shift_ratio_analytic_check = json.loads((BASE / "shift-ratio-results/shift_ratio_analytic_verification.json").read_text())
    estimates = json.loads((BASE / "estimate-results/estimate_search.json").read_text())
    estimates_check = json.loads((BASE / "estimate-results/estimate_verification.json").read_text())
    estimate_feedback = json.loads((BASE / "estimate-results/cancellation_rewrite_search.json").read_text())
    estimate_feedback_check = json.loads((BASE / "estimate-results/cancellation_rewrite_verification.json").read_text())
    from autonomous_report import load_latest
    autonomous = load_latest()
    from compensated_shift_report import load_latest as load_compensated
    compensated = load_compensated()
    from signed_control_report import load_latest as load_signed_control
    signed_control = load_signed_control()
    from stable_scale_report import load_latest as load_stable_scale
    stable_scale = load_stable_scale()
    from signed_mellin_transfer import load_latest as load_signed_mellin
    signed_mellin = load_signed_mellin()
    from mellin_search_report import load_latest as load_mellin_search
    mellin_search = load_mellin_search()
    from signed_correlation import load_latest as load_signed_correlation
    signed_correlation = load_signed_correlation(mellin_search.get("run_directory"))
    from signed_defect_report import load_latest as load_signed_defects
    signed_defects = load_signed_defects()
    from fractional_moment_report import load_latest as load_fractional_moments
    fractional_moments = load_fractional_moments()
    from fractional_zeta_branch_audit import load_latest as load_fractional_branches
    fractional_branches = load_fractional_branches()
    from signed_global_calibration import load_latest as load_signed_global
    signed_global = load_signed_global()
    from pole_neutral_report import load_latest as load_pole_neutral
    pole_neutral = load_pole_neutral()
    from parameter_jet_report import load_latest as load_parameter_jets
    parameter_jets = load_parameter_jets()
    from prime_error_report import load_latest as load_prime_error
    prime_error = load_prime_error()
    from prime_discrepancy_report import load_latest as load_prime_discrepancy
    prime_discrepancy = load_prime_discrepancy()
    from prime_twist_report import load_latest as load_prime_twists
    prime_twists = load_prime_twists()
    from prime_twist_coverage_report import load_latest as load_prime_twist_coverage
    prime_twist_coverage = load_prime_twist_coverage()
    from prime_oscillation_report import load_latest as load_prime_oscillation
    prime_oscillation = load_prime_oscillation()
    from fractional_remainder_report import load_latest as load_fractional_remainders
    fractional_remainders = load_fractional_remainders()
    from mertens_limit_report import load_latest as load_mertens_limits
    mertens_limits = load_mertens_limits()
    from mellin_kernel_report import load_latest as load_mellin_kernels
    mellin_kernels = load_mellin_kernels()
    from mellin_kernel_diagnostics import load_latest as load_kernel_observers
    kernel_observers = load_kernel_observers()
    from kernel_correlation_report import load_latest as load_kernel_correlations
    kernel_correlations = load_kernel_correlations()
    from lattice_synthesis_report import load_latest as load_lattice_synthesis
    lattice_synthesis = load_lattice_synthesis()
    from root_lattice_report import load_latest as load_root_lattices
    root_lattices = load_root_lattices()
    from divisor_preconditioner_report import load_latest as load_divisor_preconditioners
    divisor_preconditioners = load_divisor_preconditioners()
    from branch_center_report import load_latest as load_branch_centers
    branch_centers = load_branch_centers()
    from rational_fractional_contract_report import load_latest as load_rational_fractional_contracts
    rational_fractional_contracts = load_rational_fractional_contracts()
    from critical_defect_report import load_latest as load_critical_defects
    critical_defects = load_critical_defects()
    from divisor_dual_report import load_latest as load_divisor_duals
    divisor_duals = load_divisor_duals()
    from divisor_dual_analytic_report import load_latest as load_dual_analytical_review
    dual_analytical_review = load_dual_analytical_review()
    from signed_gap_profile_report import load_latest as load_signed_gap_profiles
    signed_gap_profiles = load_signed_gap_profiles()
    from signed_gap_cofinal_report import load_latest as load_signed_gap_cofinal
    signed_gap_cofinal = load_signed_gap_cofinal()
    from candidate_review_report import load_latest as load_candidate_reviews
    candidate_reviews = load_candidate_reviews()
    if candidate_reviews['status'] != 'not_run':
        from detector_workflow_guard import witness_derived_refutations
        checked_exclusions = witness_derived_refutations(candidate_reviews['round_directory'])
        if set(checked_exclusions['all_refuted_candidate_ids']) != set(candidate_reviews['all_refuted_candidate_ids']):
            raise ValueError('Refutation exclusions differ from rechecked actual witnesses')
    from inverse_prefix_report import load_latest as load_inverse_prefix
    inverse_prefix = load_inverse_prefix()
    from inverse_prefix_review_report import load_latest as load_inverse_prefix_reviews
    inverse_prefix_reviews = load_inverse_prefix_reviews()
    from workflow_audit_report import load_latest as load_workflow_audit
    workflow_audit = load_workflow_audit()
    from signed_arithmetic_report import load_latest as load_signed_arithmetic
    signed_arithmetic = (summarize_signed_arithmetic(args.signed_arithmetic_run_dir)
                         if args.signed_arithmetic_only else load_signed_arithmetic())
    from signed_arithmetic_review_report import load_latest as load_signed_arithmetic_reviews
    signed_arithmetic_reviews = load_signed_arithmetic_reviews()
    certified_keys = {(x["root_order"], x["operator"]["prime"], x["operator"]["parameter"])
                      for x in carry["certificates"] if x["certifies_no_correction_zeros_Re_s_gt_half"]}
    certified_keys |= {(x["root_order"], x["operator"]["prime"], x["operator"]["parameter"])
                       for x in schur["records"] if x["certifies_nonzero_correction_Re_s_gt_half"]}
    certified_count = len(certified_keys)
    required_keys = {(x["root_order"], x["operator"]["prime"], x["operator"]["parameter"])
                     for x in carry["certificates"]}
    assert certified_keys == required_keys
    assert carry_verification["all_passed"] and schur_controls["all_passed"]
    assert transfer["formal_checks"]["all_checks_passed"] and transfer_check["all_passed"]
    assert transfer["uniform_nonzero_correction_Re_s_gt_half_proved"] and transfer_analytic["all_passed"]
    assert global_["formal_checks"]["all_passed"] and global_analytic["all_passed"]
    assert global_["independent_bit_partition_and_mask_coefficients_agree"]
    assert dyadic["exact_operator_checks"]["all_passed"] and dyadic_check["all_passed"]
    assert dyadic["uniform_real_parameter_certificate"]["strict_zero_free_bound_proved"]
    assert dyadic_analytic["all_passed"]
    assert projection["formal_checks"]["all_passed"] and projection_check["all_passed"]
    assert projection_analytic["all_passed"] and (BASE / "projection_proof.txt").is_file()
    assert projection_analytic_check["all_passed"]
    assert projection_analytic["own_zero_in_zeta_zero_free_region_control"]["automatic_zero_preservation_rejected"]
    assert projection["commutator_search"]["all_finite_support_checks_passed"]
    assert coupling_check["all_passed"] and coupling_analytic["all_passed"] and coupling_analytic_check["all_passed"]
    assert coupling["generic_first_other_prime_module_checks"]["all_passed"]
    assert all(x["all_passed"] for x in coupling["dense_integer_validation"])
    assert coupling["factorial_grammar"]["same_formula_arity_one_negative_control_rejected"]
    assert (BASE / "coupling_proof.txt").is_file()
    assert not coupling_analytic["full_commutator_half_plane_continuation_proved"]
    assert not coupling_analytic["new_RH_estimate_proved"]
    assert size["exact_operator_checks"]["all_passed"] and size_check["all_passed"]
    assert size["paired_root_identity"]["all_passed"] and size["known_unitary_convolution_calibration_passed"]
    assert size_analytic["all_passed"] and size_analytic_check["all_passed"]
    assert (BASE / "size_carry_proof.txt").is_file()
    assert size_check["checks"]["composite_base_resonance_homomorphism_rejected"]
    assert not size_analytic["individual_half_plane_continuation_proved"]
    assert not size_analytic["new_RH_estimate_proved"]
    assert size_resonance["all_passed"] and size_resonance_check["all_passed"]
    assert size_resonance["full_H_half_plane_holomorphic_root_lift_gate_rejected"]
    assert size_resonance["no_finite_real_power_pole_cancellation_of_U_is_holomorphic_at_one"]
    assert size_resonance["paired_root_identity_not_rejected"]
    assert (BASE / "size_resonance_proof.txt").is_file()
    assert joint["all_passed"] and joint_check["all_passed"]
    assert joint_analytic["all_passed"] and joint_analytic_check["all_passed"]
    assert joint["natural_boundary_Re_s_eq_one_proved_for_finite_q_ge_2"]
    assert joint["multiplicative_independence_required"]
    assert not joint["arbitrary_many_inverse_logs_independence_claimed"]
    assert not joint["counts_as_new_primitive"] and not joint_analytic["new_RH_estimate_proved"]
    assert joint["paired_single_base_identity_not_invalidated"]
    assert (BASE / "joint_size_proof.txt").is_file()
    assert cancellation["all_passed"] and cancellation_check["all_passed"]
    assert cancellation_analytic["all_passed"] and cancellation_analytic_check["all_passed"]
    assert len(cancellation["frequency_grammar"]["survivors"]) == 1
    assert cancellation["frequency_grammar"]["survivors"][0]["q"] == 2
    assert cancellation["frequency_grammar"]["survivors"][0]["weights"] == [1, 1, 1, 1]
    assert cancellation["averaging_order_counterexample"]["averaging_and_taking_q_fold_lifts_are_not_interchangeable"]
    assert cancellation_analytic["fresh_actual_critical_line_zero_control"]["all_passed"]
    assert not cancellation["counts_as_new_primitive"] and not cancellation_analytic["new_RH_estimate_proved"]
    assert (BASE / "cancellation_proof.txt").is_file()
    assert mixed_index["all_passed"] and mixed_index_check["all_passed"]
    assert mixed_index_analytic["all_passed"] and mixed_index_analytic_check["all_passed"]
    assert len(mixed_index["parity_recurrence_grammar"]["survivors"]) == 1
    assert mixed_index["parity_recurrence_grammar"]["survivors"][0]["endpoint"] == "v2"
    assert mixed_index["arithmetic_features"]["ordinary_root_interpretation_counterexample"]["ordinary_root_interpretation_rejected"]
    assert mixed_index_analytic["existing_actual_zero_new_operator_controls"]["all_passed"]
    assert not mixed_index["counts_as_verified_new_operator"] and not mixed_index_analytic["new_RH_estimate_proved"]
    assert (BASE / "mixed_index_proof.txt").is_file()
    assert difference["all_passed"] and difference_check["all_passed"]
    assert difference_analytic["all_passed"] and difference_analytic_check["all_passed"]
    assert difference["finite_difference_calibration"]["survivors"][0]["weights"] == [-1, 3, -3, 1]
    assert len(difference["cancellation_order_grammar"]["survivors"]) == len(difference["leading_recurrence_grammar"]["survivors"]) == 1
    assert difference_analytic["ordinary_D_roots_preserved"]
    assert difference_analytic["existing_actual_zero_new_operator_controls"]["all_passed"]
    assert difference_analytic["actual_trivial_zero_control"]["one_simple_trivial_zeta_zero_certified"]
    assert difference_analytic["negative_domain_claim_is_grouped_continuation"]
    assert not difference["counts_as_verified_new_operator"] and not difference_analytic["new_RH_estimate_proved"]
    assert (BASE / "difference_proof.txt").is_file()
    assert pair["all_passed"] and pair_check["all_passed"]
    assert pair_analytic["all_passed"] and pair_analytic_check["all_passed"]
    assert pair["universal_root_constraint_grammar"]["all_survivors_linear"]
    assert len(pair["input_root_amplitude_grammar"]["survivors"]) == len(pair["inverse_mass_recurrence_grammar"]["survivors"]) == 1
    assert pair["odd_quotient_controls"]["all_passed"]
    assert pair_analytic["ordinary_Dirichlet_series_correction_convergence_proved"]
    assert pair_analytic["existing_actual_zero_new_operator_controls"]["all_passed"]
    assert not pair["historical_novelty_established"] and not pair_analytic["new_RH_estimate_proved"]
    assert (BASE / "pair_proof.txt").is_file()
    assert decode["all_passed"] and decode_check["all_passed"]
    assert decode_analytic["all_passed"] and decode_analytic_check["all_passed"]
    assert len(decode["decoder_grammar"]["survivors"]) == 1
    assert decode["decoder_grammar"]["survivors"][0]["exponent_mode"] == "full"
    assert decode["decoder_grammar"]["survivors"][0]["modulus"] == 3
    assert decode["generic_decoder_identity"]["all_passed"]
    assert decode["generic_linear_decoder_encoder_laws"]["all_passed"]
    assert decode["zeta_decoded_profile"]["formula_passed"]
    assert decode["native_factor_entry_regression"]["wrong_last_entry_dictionary_rejected"]
    assert decode["norm_loss_profiles"]["same_halfplane_bounded_decoder_rejected"]
    assert decode["raw_zeta_action_reduces_to_known_mask"]
    assert not decode["prefix_and_unavailable_input_controls"]["unavailable_query_may_be_replaced_by_zero"]
    assert not decode["all_prime_power_fibres_injective_claimed"]
    assert not fibres["all_prime_power_fibres_injective_claimed"]
    assert fibres["integer_input_probe"]["collision_count"] > 0
    assert decode_analytic["restored_actual_zero_obstruction_controls"]["all_passed"]
    assert decode_analytic_check["restored_actual_zero_obstruction_controls"]["all_passed"]
    assert decode_analytic["decoder_preserves_same_analytic_halfplane_rejected"]
    assert not decode["historical_novelty_established"] and not decode_analytic["new_RH_estimate_proved"]
    assert (BASE / "decode_proof.txt").is_file()
    assert prime_pair["all_passed"] and prime_pair_check["all_passed"]
    assert prime_pair_analytic["all_passed"] and prime_pair_analytic_check["all_passed"]
    assert len(prime_pair["prime_pair_decoder_grammar"]["survivors"]) == 1
    assert prime_pair["generic_two_product_bridge"]["all_passed"]
    assert prime_pair["zeta_profile"]["sum_formula_passed"] and prime_pair["zeta_profile"]["product_formula_passed"]
    assert prime_pair["information_loss_controls"]["two_sided_inverse_rejected"]
    assert prime_pair["hilbert_row_norm_profiles"]["unweighted_l2_boundedness_rejected"]
    assert prime_pair["weighted_norm_profiles"]["prime_only_component_endpoint_improvement"]["absolute_convergence_at_endpoint"]
    assert prime_pair_analytic["full_prime_product_zero_obstruction_controls"]["all_passed"]
    assert prime_pair_analytic_check["full_prime_product_zero_obstruction_controls"]["all_passed"]
    assert not prime_pair["counts_as_new_primitive"] and not prime_pair["all_prime_power_injectivity_claimed"]
    assert not prime_pair_analytic["additive_critical_strip_continuation_or_RH_estimate_proved"]
    assert not prime_pair["historical_novelty_established"] and not prime_pair_analytic["new_RH_estimate_proved"]
    assert (BASE / "prime_pair_proof.txt").is_file()
    assert visible["all_passed"] and visible_check["all_passed"]
    assert visible_analytic["all_passed"] and visible_analytic_check["all_passed"]
    assert len(visible["single_visible_classifier_grammar"]["survivors"]) == 1
    assert len(visible["same_prime_reconstruction_grammar"]["survivors"]) == 1
    assert len(visible["local_cancellation_grammar"]["order_survivors"]) == 1
    assert len(visible["local_cancellation_grammar"]["leading_survivors"]) == 1
    assert visible["generic_filtered_bilinear_identity"]["all_passed"]
    assert all(row["formula_passed"] for row in visible["zeta_profiles"])
    assert visible["weighted_norm_profiles"]["kernel_decoded_to_zero"]
    assert visible["weighted_norm_profiles"]["unqualified_Hilbert_boundary_norm_one_rejected"]
    assert visible["weighted_norm_profiles"]["full_encoded_endpoint_converges"]
    assert visible_analytic["full_encoded_endpoint_convergence_proved_by_PNT"]
    assert visible_analytic["deep_correction_ball_checks"]["all_passed"]
    assert visible_analytic_check["deep_correction_ball_checks"]["all_passed"]
    assert visible_analytic["restored_actual_zero_obstruction_controls"]["all_passed"]
    assert visible_analytic_check["restored_actual_zero_obstruction_controls"]["all_passed"]
    assert len(visible_analytic["actual_zeta_ball_checks"]) == 6
    assert len(visible_analytic["deep_correction_ball_checks"]["records"]) == 6
    assert len(visible_analytic["restored_actual_zero_obstruction_controls"]["records"]) == 8
    assert not visible["global_prime_power_injectivity_claimed"]
    assert not visible["historical_novelty_established"] and not visible_analytic["new_RH_estimate_proved"]
    assert (BASE / "visible_proof.txt").is_file()
    assert all(data["all_passed"] for data in (gap_probe, gap, gap_check, gap_analytic, gap_analytic_check))
    assert len(gap_probe["scaling_threshold_grammar"]["survivors"]) == 1
    assert gap_probe["numerical_energy_is_double_precision_exploration_only"]
    assert gap["generic_operator_laws"]["all_passed"]
    assert gap["inverse_mass_grammar"]["all_two_seed_survivors_rejected_on_collision_seeds"]
    assert gap["inverse_mass_grammar"]["universal_mass_minus_overlap_identity_passed"]
    assert gap["positive_semidefinite_kernel_rejected"]["negative_coefficient_six"] == "-2"
    assert gap_check["zeta_audit"]["encoded_indices_checked"] == 40955
    assert gap["endpoint_divergence_r_two"] and gap["endpoint_converges_iff"] == "r=1 or r>=3"
    assert len(gap_analytic["actual_zeta_ball_checks"]) == 6
    assert len(gap_analytic["transformed_ordinary_root_scalar_controls"]["records"]) == 5
    assert len(gap_analytic["one_sided_actual_zero_controls"]["records"]) == 6
    assert gap_analytic["selected_r_three_correction_continuous_Re_ge_half"]
    assert gap_analytic["classical_prime_pair_correlation_kernel_matched"]
    assert not gap_analytic["whole_critical_zero_disk_holomorphy_established"]
    assert not gap["counts_as_new_primitive"] and not gap["historical_novelty_established"]
    assert not gap_analytic["new_RH_estimate_proved"]
    assert (BASE / "gap_proof.txt").is_file()
    assert all(data["all_passed"] for data in (laplacian,laplacian_check,laplacian_analytic,laplacian_analytic_check))
    assert laplacian["diagonal_completion_grammar"]["survivors"][0]["weights"] == [1,-2,1]
    assert laplacian["support_mask_grammar"]["surviving_masks"] == ["prime","odd"]
    assert laplacian["support_mask_grammar"]["complete_sparse_composition_no_encoded_prefix_cutoff"]
    assert all(row["square_positive_nonsquare_negative"] for row in laplacian["zeta_profiles"])
    assert laplacian_check["zeta_audit"]["encoded_indices_checked"] == 32764
    assert len(laplacian_analytic["actual_zeta_ball_checks"]) == 6
    assert len(laplacian_analytic["ordinary_root_scalar_controls"]["records"]) == 5
    assert len(laplacian_analytic["whole_actual_zero_correction_controls"]["records"]) == 2
    assert all(row["whole_zero_disk_correction_holomorphic"] for row in laplacian_analytic["whole_actual_zero_correction_controls"]["records"])
    assert laplacian_analytic["grouped_correction_holomorphic_domain"] == "Re(s)>1/3"
    assert laplacian_analytic["ordinary_correction_absolute_abscissa"] == "1/2, endpoint convergent"
    assert not laplacian["counts_as_new_primitive"] and not laplacian["historical_novelty_established"]
    assert not laplacian_analytic["new_RH_estimate_proved"]
    assert (BASE / "laplacian_proof.txt").is_file()
    assert all(data["all_passed"] for data in (moment,moment_check,moment_analytic,moment_analytic_check))
    assert len(moment["moment_annihilation_grammar"]["bounded_search"]) == 2
    assert moment["gap_minimum"] == 2 and moment["only_removed_prime_edge"] == [2,3]
    assert moment["gap_support_mask_grammar"]["smallest_stable_gap_mask"] == 2
    assert moment["gap_support_mask_grammar"]["finite_floating_point_discovery_only"]
    assert moment["image_scale_fit"]["fits"] == [{"A":4,"B":6,"held_out_passed":True}]
    assert moment_check["zeta_audit"]["complete_prefix_indices_checked"] == 16382
    assert moment_check["zeta_audit"]["finite_prime_input_encoded_queries"] == 4764
    assert len(moment_analytic["correction_native_zeta_auxiliary_groups"]["records"]) == 6
    assert len(moment_analytic["ordinary_root_auxiliary_controls"]["records"]) == 5
    assert len(moment_analytic["whole_actual_zero_root_controls"]["records"]) == 8
    assert moment_analytic["unmasked_coefficientwise_limit_counterexample"]["coefficientwise_identity_implies_scalar_identity_rejected"]
    assert moment_analytic["new_full_coefficient_origin_comparison_groups"] == 0
    assert all(row["ordinary_correction_series_absolute_on_whole_disk"] for row in moment_analytic["whole_actual_zero_root_controls"]["records"])
    assert not moment["counts_as_new_primitive"] and not moment["historical_novelty_established"]
    assert not moment_analytic["new_RH_estimate_proved"]
    assert (BASE / "moment_proof.txt").is_file()
    assert all(data["all_passed"] for data in (radix,radix_check,radix_analytic,radix_analytic_check))
    assert [row["radix"] for row in radix["log_polynomial_grammar"]["records"]] == [2,3,4,5,7]
    assert all(row["inferred_polynomial_degree"] == row["radix"]-1
               and row["held_out_passed"] and row["leading_scale_identity_passed"]
               for row in radix["log_polynomial_grammar"]["records"])
    assert radix["log_polynomial_grammar"]["radix_degree_fits"] == [{"slope":1,"intercept":-1,"held_out_passed":True}]
    assert radix_check["encoded_zeta_indices_checked"] == 40950
    assert len(radix_check["checks"]) == 5 and len(radix_analytic_check["checks"]) == 6
    assert not radix_check["production_imports"] and not radix_analytic_check["production_imports"]
    assert radix["composite_radix_binomial_filter_negative_control"]["nonassociative_replacement_rejected"]
    assert len(radix_analytic["actual_zeta_ball_checks"]) == 6
    assert len(radix_analytic["leading_self_similarity_controls"]["records"]) == 4
    assert len(radix_analytic["ordinary_root_auxiliary_controls"]["records"]) == 5
    assert radix["ordinary_output_root_fidelity"] == radix_analytic["ordinary_root_location_fidelity"] == "rejected"
    assert radix_analytic["created_operator_zero"]["exactly_one_simple_transformed_zero_certified"]
    assert radix_analytic["created_operator_zero"]["Euler_to_local_LOG_corridor"]["all_passed"]
    assert not radix_analytic["created_operator_zero"]["ordinary_zeta_zero_in_this_disk"]
    assert not radix_analytic["created_operator_zero"]["new_ordinary_zeta_zero_located"]
    assert radix_analytic_check["created_operator_zero_audit"]["same_nested_simple_operator_zero_certified"]
    assert radix_analytic_check["created_operator_zero_audit"]["disk_centre"] == radix_analytic["created_operator_zero"]["disk_centre"]
    assert radix_analytic_check["created_operator_zero_audit"]["radius"] == "1/200000"
    assert radix_analytic["single_loop_blind_spot_control"]["first_jump_is_exactly_zero_by_constructed_model"]
    assert radix_analytic["single_loop_blind_spot_control"]["second_difference_is_nonzero_by_universal_H_bound"]
    assert len(radix_analytic["actual_zeta_zero_branch_ladder_controls"]["records"]) == 2
    assert not radix["counts_as_new_primitive"] and not radix["historical_novelty_established"]
    assert not radix_analytic["new_RH_estimate_proved"]
    assert (BASE / "radix_proof.txt").is_file()
    assert all(data["all_passed"] for data in (prime_scale,prime_scale_check,prime_scale_analytic,prime_scale_analytic_check))
    assert len(prime_scale_check["checks"]) == len(prime_scale_analytic_check["checks"]) == 6
    assert not prime_scale_check["production_imports"] and not prime_scale_analytic_check["production_imports"]
    assert prime_scale["prime_extraction_grammar"]["survivors"] == [{"atom":"mu","power":-1,"training_passed":True,"held_out_passed":True}]
    assert prime_scale["prime_extraction_grammar"]["generic_power_lift_inverse_control"]["two_inverse_laws_verified"]
    assert prime_scale["floor_filter_grammar"]["models_scored"] == 78125
    assert prime_scale["floor_filter_grammar"]["coarse_grid_survivors"] == 341
    assert len(prime_scale["floor_filter_grammar"]["certified_positive_filters"]) == 67
    assert prime_scale["floor_filter_grammar"]["height_one_count"] == 15
    assert prime_scale["floor_filter_grammar"]["height_two_count"] == 52
    assert prime_scale["floor_filter_grammar"]["first_coarse_grid_alias"]["actual_factorial_ratio"] == "1/4"
    assert len(prime_scale["universal_scale_identity_controls"]["floor_trace_exact_groups"]) == 180
    assert len(prime_scale["actual_prime_scale_observations"]["records"]) == 24
    assert prime_scale["actual_prime_scale_observations"]["largest_sampled_integer"] == 10**12+4096
    assert not prime_scale["actual_prime_scale_observations"]["universal_count_or_gap_bound_inferred_from_samples"]
    assert prime_scale_check["observation_audit"]["complete_windows_checked"] == 24
    assert len(prime_scale_analytic["actual_zeta_ball_checks"]) == 6
    assert len(prime_scale_analytic["floor_trace_Mellin_auxiliary_checks"]["records"]) == 6
    assert len(prime_scale_analytic["actual_zeta_zero_erasure_and_decoded_pole_controls"]["records"]) == 2
    assert prime_scale_analytic["actual_zeta_zero_erasure_and_decoded_pole_controls"]["unmodified_floor_trace_RH_holomorphy_gate_rejected"]
    assert prime_scale_analytic["scale_decoder_norm_controls"]["generic_scale_decoder_bounded_iff_sigma_gt_one_proved"]
    assert not prime_scale_analytic["scale_decoder_norm_controls"]["prime_specific_cancellation_improvement_ruled_out"]
    assert len(prime_scale["prime_information_priority"]["candidate_triage"]) == 10
    assert not prime_scale["counts_as_new_operator"] and not prime_scale["historical_novelty_established"]
    assert not prime_scale_analytic["new_uniform_prime_distribution_estimate_proved"]
    assert not prime_scale_analytic["new_RH_estimate_proved"]
    assert (BASE / "prime_scale_proof.txt").is_file()
    assert all(data["all_passed"] for data in (qrh,qrh_check,creative,creative_check,global_moment,global_moment_check))
    assert len(qrh_check["checks"]) == len(creative_check["checks"]) == 6
    assert len(global_moment_check["checks"]) == 7
    assert not qrh_check["production_imports"] and not creative_check["mathematical_audit_imports_production_code"]
    assert creative_check["integration_checks_import_production_code"]
    assert qrh["Gauss_conversion_recovery"]["programs_scored"] == 432
    assert len(qrh["Gauss_conversion_recovery"]["survivors"]) == 1
    assert qrh_check["native_Fourier_identities"] == 816
    assert not qrh["full_theta_reflection_implemented"]
    assert not qrh["global_mean_square_bounds_independently_verified"]
    assert not qrh["entire_QRH_proof_independently_verified"]
    assert creative["operator_word_search"]["map_programs_evaluated"] == 11111
    assert not creative["operator_word_search"]["numerical_aliases_promoted_to_theorems"]
    assert creative["inverse_Fourier_projection_discovery"]["minimal_positive_projection_power"] == 2
    assert creative["commutator_defect_search"]["observed_lead"]["universal_rank_equality_proved"]
    assert creative["nonassociative_phase_search"]["phase_product_programs"] == 16
    assert creative["learned_phase_kernel_search"]["unknown_coefficients"] == 10
    assert creative["learned_phase_kernel_search"]["universal_kernel_span_dimension"] == 4
    assert len(creative["learned_phase_kernel_search"]["cross_prime_false_law_controls"]) == 6
    assert creative_check["public_entry_point_audit"]["fresh_prime_learned_kernel_executions"] == 4
    assert creative_check["public_entry_point_audit"]["normalized_QRH_scalar_executions"] == 7
    assert not creative["zeta_coefficient_residue_bridge"]["ordinary_zeta_zero_fidelity_after_embedding_proved"]
    assert not creative["new_uniform_prime_distribution_estimate_proved"] and not creative["new_RH_estimate_proved"]
    assert creative["verified_new_operators"] == []
    assert (BASE / "creative_grammar_proof.txt").is_file()
    assert not global_moment_check["mathematical_audit_imports_production_code"]
    assert global_moment_check["integration_checks_import_production_code"]
    assert global_moment["generic_operator_moment_transfer_search"]["operator_programs_scored"] == 48
    assert len(global_moment["generic_operator_moment_transfer_search"]["universally_certified_transfers"]) == 24
    assert len(global_moment["generic_operator_moment_transfer_search"]["finite_training_recurrences_rejected"]) == 16
    assert [r["minimum_growth_rate"] for r in global_moment["positive_functional_search"]["records"]] == [4,6]
    assert not global_moment["anti_overfit_protocol"]["QRH_global_bound_used_as_training_target"]
    assert not global_moment["QRH_global_moment_bound_independently_verified"]
    assert not global_moment["new_uniform_prime_distribution_estimate_proved"]
    assert not global_moment["ordinary_zeta_zero_bridge_proved"] and global_moment["verified_new_operators"] == []
    assert global_moment["moment_to_arithmetic_target_transfer"]["learned_moment_and_row_count_powers"] == ['1/2','-1/2']
    assert not global_moment["moment_to_arithmetic_target_transfer"]["all_scale_prime_row_count_and_error_certificates_supplied"]
    assert not global_moment["moment_to_arithmetic_target_transfer"]["new_Mobius_or_prime_target_bound_established"]
    assert (BASE / "global_moment_proof.txt").is_file()
    assert fractional["all_passed"] and fractional_check["all_passed"]
    assert fractional_analytic["all_passed"] and fractional_analytic_check["all_passed"]
    assert len(fractional_check["checks"]) == 7 and all(fractional_check["checks"].values())
    assert len(fractional_analytic_check["checks"]) == 6 and all(fractional_analytic_check["checks"].values())
    assert not fractional_check["mathematical_audit_imports_production_code"]
    assert fractional_check["integration_checks_import_production_code"]
    assert fractional_check["public_entry_point_audit"]["real_and_complex_changed_input_executions"] == 32
    assert fractional_check["public_entry_point_audit"]["invalid_program_controls_rejected"] == 9
    assert not fractional_analytic_check["production_imports"]
    import hashlib
    assert fractional_analytic_check["source_artifact_sha256"] == hashlib.sha256((BASE / "fractional-prime-results/fractional_prime_analytic.json").read_bytes()).hexdigest()
    assert fractional["all_integer_sharp_uniform_composite_bound_proved"]
    assert fractional["all_integer_nonzero_sign_rule_proved"]
    assert not fractional["coefficient_production_uses_prime_indicator_or_prime_weights"]
    assert not fractional["historical_novelty_established"] and not fractional["new_uniform_prime_distribution_estimate_proved"]
    assert len(fractional_analytic["actual_zeta_ball_checks"]) == 6
    assert not fractional_analytic["full_normalized_B_decoder_native_value_compared"]
    assert not fractional_analytic["new_RH_estimate_proved"]
    assert not fractional_analytic["fractional_numerator_and_decoder_actual_zero_controls"]["global_nonvanishing_of_fractional_numerator_at_every_zeta_zero_proved"]
    assert (BASE / "fractional_prime_proof.txt").is_file() and (BASE / "fractional_prior_art_audit.txt").is_file()
    assert prime_moment["all_passed"] and prime_moment_check["all_passed"]
    assert len(prime_moment["generic_affine_moment_search"]["programs"]) == 12
    assert not prime_moment["generic_affine_moment_search"]["prime_or_QRH_target_used_in_training"]
    assert len(prime_moment["actual_arithmetic_moment_count_bridge"]["records"]) == 16
    assert not prime_moment["actual_arithmetic_moment_count_bridge"]["prime_labels_supplied_to_moment_program"]
    assert len(prime_moment_check["checks"]) == 6 and all(prime_moment_check["checks"].values())
    assert not prime_moment_check["mathematical_audit_imports_production_code"]
    assert prime_moment_check["integration_checks_import_production_code"]
    assert prime_moment_check["public_entry_point_audit"]["public_executions"] == 38
    assert prime_moment_check["public_entry_point_audit"]["invalid_contract_controls_rejected"] == 13
    assert prime_moment["separate_all_scale_energy_estimate_supplied"]
    assert prime_moment["known_sieve_all_scale_energy_upper_bound_supplied"]
    assert not prime_moment["new_independent_prime_distribution_estimate_supplied"]
    assert prime_moment["prime_roughness_and_all_scale_moment_certificate"]["critical_envelope_loglog_cost_retained"]
    assert not prime_moment["prime_roughness_and_all_scale_moment_certificate"]["stronger_actual_critical_moment_bound_ruled_out"]
    assert prime_moment_check["prime_roughness_audit"]["independent_doubling_moments_checked"] == 72
    assert not prime_moment_check["prime_roughness_audit"]["external_full_sieve_proof_independently_verified"]
    assert not prime_moment["ordinary_zeta_zero_bridge_for_Hadamard_moment_operators_proved"]
    assert not prime_moment["new_uniform_prime_distribution_estimate_proved"]
    assert not prime_moment["coefficient_even_moments_equal_ordinary_circle_even_moments_claimed"]
    assert prime_moment["verified_new_operators"] == [] and (BASE / "prime_moment_transfer_proof.txt").is_file()
    assert (BASE / "prime_roughness_moment_proof.txt").is_file()
    assert shift_ratio["all_passed"] and shift_ratio_check["all_passed"]
    assert shift_ratio_analytic["all_passed"] and shift_ratio_analytic_check["all_passed"]
    assert len(shift_ratio_check["checks"]) == 7 and all(shift_ratio_check["checks"].values())
    assert len(shift_ratio_analytic_check["checks"]) == 6 and all(shift_ratio_analytic_check["checks"].values())
    assert shift_ratio_check["coefficient_audit"]["independent_subset_coefficients_checked"] == 16380
    assert shift_ratio_check["public_entry_point_audit"]["public_executions"] == 53
    assert shift_ratio_check["public_entry_point_audit"]["invalid_contracts_rejected"] == 24
    assert not shift_ratio_check["mathematical_audit_imports_production_code"]
    assert shift_ratio_check["integration_checks_import_production_code"]
    assert not shift_ratio_analytic_check["production_imports"]
    assert shift_ratio_check["source_artifact_sha256"] == hashlib.sha256((BASE / "shift-ratio-results/shift_ratio_search.json").read_bytes()).hexdigest()
    assert shift_ratio_analytic_check["source_artifact_sha256"] == hashlib.sha256((BASE / "shift-ratio-results/shift_ratio_analytic.json").read_bytes()).hexdigest()
    assert shift_ratio_analytic["complete_B_native_comparisons"] == 6
    assert all(r["complete_B_decoder_native_value_compared"] for r in shift_ratio_analytic["actual_zeta_ball_checks"])
    assert shift_ratio["all_zero_orders_local_signature_proved"] and shift_ratio["pole_regularized_RH_equivalence_proved"]
    assert not shift_ratio["coefficient_production_uses_prime_indicator_or_prime_weights"]
    assert not shift_ratio["historical_novelty_established"] and shift_ratio["verified_new_operators"] == []
    assert not shift_ratio["new_independent_prime_distribution_estimate_proved"] and not shift_ratio["new_RH_estimate_proved"]
    assert (BASE / "shift_ratio_proof.txt").is_file() and (BASE / "shift_ratio_prior_art_audit.txt").is_file()
    assert estimates["all_passed"] and estimates_check["all_passed"]
    assert len(estimates_check["checks"]) == 6 and all(estimates_check["checks"].values())
    assert estimates_check["source_artifact_sha256"] == hashlib.sha256((BASE / "estimate-results/estimate_search.json").read_bytes()).hexdigest()
    for key, name in (("producer_code_sha256", "estimate_search.py"),
                      ("grammar_code_sha256", "estimate_grammar.py"), ("proof_sha256", "estimate_proof.txt")):
        assert estimates[key] == hashlib.sha256((BASE / name).read_bytes()).hexdigest()
    assert estimates_check["checker_code_sha256"] == hashlib.sha256((BASE / "check_estimates.py").read_bytes()).hexdigest()
    assert estimates_check["arithmetic_and_fit_audit"]["replayed_growth_proposals"] == 700
    assert estimates_check["arithmetic_and_fit_audit"]["independently_factored_inverse_coefficients"] == 131072
    assert estimates_check["positive_energy_audit"]["exact_and_changed_variable_integral_certificates"] == 12
    assert estimates_check["positive_energy_audit"]["strict_improvements_over_supplied_Jensen_constants"] == 2
    assert not estimates_check["mathematical_audit_imports_production_code"]
    assert not estimates["production_coefficient_engine_uses_prime_or_factor_oracle"]
    assert not estimates["new_RH_estimate_proved"] and not estimates["new_independent_prime_distribution_estimate_proved"]
    assert estimates["verified_new_operators"] == []
    assert estimate_feedback["all_passed"] and estimate_feedback_check["all_passed"]
    assert len(estimate_feedback_check["checks"]) == 5 and all(estimate_feedback_check["checks"].values())
    assert estimate_feedback_check["source_artifact_sha256"] == hashlib.sha256((BASE / "estimate-results/cancellation_rewrite_search.json").read_bytes()).hexdigest()
    assert estimate_feedback["source_estimate_search_sha256"] == estimates_check["source_artifact_sha256"]
    assert estimate_feedback["source_estimate_verification_sha256"] == hashlib.sha256((BASE / "estimate-results/estimate_verification.json").read_bytes()).hexdigest()
    for key, name in (("producer_code_sha256", "cancellation_rewrite_search.py"),
                      ("grammar_code_sha256", "cancellation_rewrite_grammar.py"), ("proof_sha256", "cancellation_rewrite_proof.txt")):
        assert estimate_feedback[key] == hashlib.sha256((BASE / name).read_bytes()).hexdigest()
    assert estimate_feedback_check["checker_code_sha256"] == hashlib.sha256((BASE / "check_cancellation_rewrites.py").read_bytes()).hexdigest()
    assert estimate_feedback["proved_affine_bounds"] == 280
    assert not estimate_feedback_check["mathematical_audit_imports_production_code"]
    assert not estimate_feedback["sublinear_cancellation_certificate_discovered"]
    assert not estimate_feedback["new_independent_prime_distribution_estimate_proved"] and not estimate_feedback["new_RH_estimate_proved"]
    assert estimate_feedback["verified_new_operators"] == []
    assert all(x["proof_audit"]["status"] == "proved_classical_root_lowering" for x in shift["surviving_candidates"])
    matches = root["root_grammar"]["matches"]
    denominator_matches = [match for record in root["denominator_search"]
                           for match in record["training_matches"]]
    denominator_survivors = [match for match in denominator_matches if match["held_out_passed"]]
    denominator_rejected = [match for match in denominator_matches if not match["held_out_passed"]]
    sources = [
        {"id": "fractional_divisor_functions", "authors": "Hideki Nakaya", "year": 1993,
         "title": "On the Generalized Divisor Problem",
         "url": "https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/0837-09.pdf",
         "evidence": "Page 1 defines coefficients d_z through zeta(s)^z for complex z, with the normalized logarithm. Root coefficients are instances of this established family."},
        {"id": "formal_log_exp", "authors": "Huilan Li and Trueman MacHenry", "year": 2010,
         "title": "The Convolution Ring of Arithmetic Functions and Symmetric Polynomials",
         "url": "https://arxiv.org/abs/1009.1892",
         "evidence": "Introduces arithmetic logarithm and exponential operators in an established formal convolution setting, with earlier work attributed to Rearick. This supports prior-art status of arithmetic LOG/EXP; exact conventions need comparison."},
        {"id": "rearick_log_exp_and_prime_derivations", "authors": "Wai Yan Pong", "year": 2016,
         "title": "Applications of differential algebra to algebraic independence of arithmetic functions",
         "url": "https://www.impan.pl/shop/publication/transaction/download/product/91275",
         "evidence": "Section 2 gives the coefficient-local formal exponential/logarithm used here and the prime-basic derivation underlying recovered lowering recurrences; attributes the operators to Rearick (1968)."},
        {"id": "nonzero_kernel_classification", "authors": "Ingrid Popa Fotino", "year": 1975,
         "title": "Generalized convolution ring of arithmetic functions",
         "url": "https://msp.org/pjm/1975/61-1/pjm-v61-n1-p11-s.pdf",
         "evidence": "Classifies nonvanishing associative divisor kernels; the symmetric case is a scalar-weight transport. This motivates searching degenerate products and nonlinear transfers beyond these known coordinate changes."},
        {"id": "roots_of_multiplicative_functions", "authors": "Tim Carroll and A. A. Gioia", "year": 1988,
         "title": "Roots of multiplicative functions",
         "url": "https://www.numdam.org/item/CM_1988__65_3_349_0.pdf",
         "evidence": "Explicit root formulas for completely multiplicative inputs, including rational powers; cites the earlier root/logarithm theory of Rearick."},
        {"id": "weighted_transport", "authors": "Pattira Ruengsinsub et al.", "year": 2012,
         "title": "Results about dependence and convolution",
         "url": "https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1806-07.pdf",
         "evidence": "Section 3 defines alpha(n)/(alpha(i)alpha(j))-weighted divisor convolution and proves its isomorphism with Dirichlet convolution. Nonzero carry weights are instances with alpha(n)=t^G(n)."},
        {"id": "binomial", "authors": "Laszlo Toth and Pentti Haukkanen", "year": 2009,
         "title": "On the binomial convolution of arithmetical functions",
         "url": "https://arxiv.org/abs/0806.0508",
         "evidence": "Defines the prime-exponent binomial kernel and studies its algebra, including its relation to Dirichlet convolution."},
        {"id": "generalized_divisibility", "authors": "J. V. Burnett, O. V. Osterman and R. Lewandowski", "year": 2019,
         "title": "On a special class of A-functions",
         "url": "https://nyjm.albany.edu/j/2019/25-57v.pdf",
         "evidence": "Discusses infinitary and structured divisibility and general arithmetic kernels. This supplies a broader prior-art framework for no-carry constructions; specific base-prime/root applications still need comparison."},
        {"id": "infinitary_classical", "authors": "Graeme L. Cohen and Peter Hagis, Jr.", "year": 1993,
         "title": "Arithmetic functions associated with the infinitary divisors of an integer",
         "url": "https://onlinelibrary.wiley.com/doi/pdf/10.1155/S0161171293000456",
         "evidence": "Section 2 explicitly defines infinitary convolution and proves its abelian unit group. Its binary component description makes exponent shifting elementary; no specific LOG/EXP zeta transfer is identified in this paper."},
        {"id": "arithmetic_cross_group_operators", "authors": "Vichian Laohakosol, Nittiya Pabhapote and Nalinee Wechwiriyakul", "year": 2001,
         "title": "Arithmetic Functions and Operators",
         "url": "https://www.scienceasia.org/2001.27.n3/v27_199_202.pdf",
         "evidence": "Reviews established arithmetic logarithms, exponentials and group isomorphisms, including prior ordinary/unitary groups. Its derivative-weighted logarithm differs by log(n) from the coefficient-local formal logarithm, so conventions were compared rather than equated."},
        {"id": "polymer_arithmetic_exp", "authors": "Pierluigi Contucci and Andreas Knauf", "year": 2001,
         "title": "The Low Activity Phase of Some Dirichlet Series (PDF version dated 2 October 2001; preprint cover 1996)",
         "url": "https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/contucci-knauf.pdf",
         "evidence": "Appendix A gives formal EXP/LOG for ordinary and exponent-binomial convolution and a partition formula. Physical cross-prime/polymer interpretations and partition exponentials are established prior art."},
        {"id": "ordered_prime_multinomial", "title": "OEIS A008480: number of ordered prime factorizations",
         "url": "https://oeis.org/A008480",
         "evidence": "The exact multinomial Omega(n)!/product_p v_p(n)! and its ordered-prime-factorization interpretation are established. The projection mask is its parity, not an undiscovered multinomial primitive."},
        {"id": "prime_indicator_inverse", "title": "OEIS A355939: inverse of the noncomposite indicator", "year": 2022,
         "url": "https://oeis.org/A355939",
         "evidence": "The ordinary inverse of delta plus the prime indicator is (-1)^Omega times the classical multinomial, with formal generating series 1/(1+P(s)). This recovered inverse is established prior art."},
        {"id": "multinomial_dirichlet_study", "authors": "Maxie Dion Schmidt", "year": 2022,
         "title": "Exact formulas for partial sums of the Mobius function expressed by partial sums weighted by the Liouville lambda function",
         "url": "https://arxiv.org/abs/2102.05842",
         "evidence": "Studies the same multinomial C_Omega, its ordered-factorization prime-zeta series, and related inverses. Its full primary text was searched for the specific parity projection/typed intertwiner without an exact match being identified; no-match is not originality evidence."},
        {"id": "bounded_exponent_factorization", "authors": "Simon Litsyn and Vladimir Shevelev", "year": 2007,
         "title": "On Factorization of Integers with Restrictions on the Exponents",
         "url": "https://zenodo.org/records/8288749",
         "evidence": "Establishes the base-(k+1) prime-power component factorization and k-arithmetic framework. This is prior art for the digit layers, not a verified publication match for the cross-prime A_b-to-G_b projection."},
        {"id": "infinitary_and_kary_algebras", "authors": "Pentti Haukkanen", "year": 2000,
         "title": "On the k-ary convolution of arithmetical functions",
         "url": "https://www.fq.math.ca/Scanned/38-5/haukkanen.pdf",
         "evidence": "Theorem 2.2 states the classical associative infinitary algebra, its unit group, and multiplicativity properties. General k-ary products can fail associativity; the present module is not promoted to an untyped product."},
        {"id": "davison_general_divisor_kernels", "authors": "T. M. K. Davison", "year": 1966,
         "title": "On Arithmetic Convolutions",
         "url": "https://www.cambridge.org/core/services/aop-cambridge-core/content/view/198C74522DE4B0F126BF0231877B01A8/S0008439500052863a.pdf/on_arithmetic_convolutions.pdf",
         "evidence": "The general divisor-kernel framework and associativity cocycle condition are classical. Its extra multiplicativity condition is distinct and need not hold for size carries. The reviewed examples do not identify the exact paired floor/ceiling identity."},
        {"id": "davison_normed_semigroups", "authors": "Stefan Porubsky", "year": 2003,
         "title": "Structure of the group of quasi multiplicative arithmetical functions",
         "url": "https://real.mtak.hu/142348/1/AAPASM_30_from133to145.pdf",
         "evidence": "Section 3 states general kernel associativity/unit conditions; section 4 treats normed free commutative semigroups. Dependence on assigned sizes alone does not establish specificity to ordinary prime distribution."},
        {"id": "classical_beta_integral", "title": "NIST DLMF 5.12.1: Euler beta integral",
         "url": "https://dlmf.nist.gov/5.12.E1",
         "evidence": "The beta integral gives (beta)_j/j! as moments of Beta(beta,1-beta), used to prove the resonance correction has positive real part for every base and beta in [0,1]."},
        {"id": "classical_elliptic_hypergeometric", "title": "NIST DLMF 19.5.1: complete elliptic integral expansion",
         "url": "https://dlmf.nist.gov/19.5.E1",
         "evidence": "The base-6 beta=1/2 correction is a classical hypergeometric/elliptic function. With NIST's modulus convention the elliptic argument is sqrt(6^-s)."},
        {"id": "classical_Hurwitz_Euler_Maclaurin", "title": "NIST DLMF 25.11: Hurwitz zeta function",
         "url": "https://dlmf.nist.gov/25.11",
         "evidence": "Euler summation and Euler-Maclaurin remainder formulas support the independent geometric-tail enclosures for J_1 and the finite arithmetic calculation of zeta's derivative."},
        {"id": "classical_zeta_zero_free_line", "title": "NIST DLMF 25.10: Riemann zeta zeros",
         "url": "https://dlmf.nist.gov/25.10",
         "evidence": "The classical zero-free line Re(s)=1 ensures that the normalized local log(zeta) has finite limits at each nonzero size harmonic. This proves the log-angle weak limit used for the U growth obstruction."},
        {"id": "classical_subset_convolution", "authors": "Andreas Bjorklund, Thore Husfeldt, Petteri Kaski and Mikko Koivisto", "year": 2006,
         "title": "Fourier meets Mobius: fast subset convolution",
         "url": "https://arxiv.org/abs/cs/0611101",
         "evidence": "Defines the exact set-bit convolution used in the shifted additive carry-free product. This establishes prior art for that primitive, without resolving the prime-power/binary application or its domain theorem."},
        {"id": "classical_Bell_partition_EGF", "title": "NIST DLMF 26.7.5: Bell generating function",
         "url": "https://dlmf.nist.gov/26.7.E5",
         "evidence": "The classical entire Bell generating function supplies the partition majorant. The weighted version follows by assigning a factor to each block; its dyadic row estimate proves the selected zeta-input positive-half-plane domain."},
        {"id": "classical_finite_difference_moments", "title": "NIST DLMF 26.8.6: Stirling finite-difference formula",
         "url": "https://dlmf.nist.gov/26.8.E6",
         "evidence": "The alternating binomial moments vanish below the difference order and equal m! at that order. The recovered third-forward-difference weights are classical; this does not resolve publication history of the iterated quadratic-index zeta application."},
        {"id": "classical_Catalan_inverse_trees", "title": "NIST DLMF 26.5: Catalan numbers",
         "url": "https://dlmf.nist.gov/26.5",
         "evidence": "The inverse-tree total masses and scalar quadratic inverse are classical Catalan constructions. Distinct integer tree labels do not make this count a new primitive."},
        {"id": "classical_Mordell_Tornheim_kernel", "title": "Mordell--Tornheim Zeta Values, Their Alternating Version, and Their Finite Analogs",
         "url": "https://arxiv.org/abs/2401.03380",
         "evidence": "The product/sum denominator is a classical multiple-zeta framework. The reviewed finite-prime analogues are different from the present LOG-zeta prime-power weights; precise compound-application originality remains unresolved."},
        {"id": "classical_scaled_Mobius_inversion", "title": "NIST DLMF 27.5.7: scaled Mobius inversion",
         "url": "https://dlmf.nist.gov/27.5.E7",
         "evidence": "Scaled Mobius inversion gives the prime-zeta reference from the Euler logarithm. It is a classical calibration, not a new operator."},
        {"id": "classical_unique_prime_factorization", "title": "NIST DLMF 27.2: fundamental theorem of arithmetic",
         "url": "https://dlmf.nist.gov/27.2",
         "evidence": "Unique prime valuations supply the power-free decomposition and residue-sector decoder proof. The decomposition and coordinate-permutation framework are classical."},
        {"id": "classical_prime_zeta_zero_singularities", "authors": "Gordon Chavez and Altan Allawala", "year": 2021,
         "title": "Prime zeta function statistics and Riemann zero-difference repulsion (reviewed primary abstract)",
         "url": "https://arxiv.org/abs/2102.02280",
         "evidence": "The reviewed abstract connects prime-zeta singular structure with Riemann zeros. Logarithmic zero obstructions are established context; the abstract supplies no match or originality proof for this specific decoder."},
        {"id": "classical_prime_number_theorem", "title": "NIST DLMF 27.12: asymptotic formulas for primes",
         "url": "https://dlmf.nist.gov/27.12",
         "evidence": "Unconditional prime density supplies sharp prime-only and full weighted-prime-power encoded abscissae and endpoint convergence, additive endpoint convergence and Hilbert row-growth necessity. None of these proofs assumes a pointwise Goldbach asymptotic."},
        {"id": "classical_Stirling_log_square_harmonics", "title": "NIST DLMF 26.8.8 and 26.8.15: logarithm generating function and harmonic two-cycle law",
         "url": "https://dlmf.nist.gov/26.8.E15",
         "evidence": "Together with the logarithm generating function at 26.8.E8, this gives coefficient 2H_(k-1)/k of (-log(1-x))^2. The learned leading cancellation coefficient is classical harmonic arithmetic, not a new primitive."},
        {"id": "classical_weighted_Goldbach_continuation", "authors": "Gautami Bhowmik and Jan-Christoph Schlage-Puchta", "year": 2010,
         "title": "Meromorphic Continuation of the Goldbach generating function (reviewed definition and theorem statements)",
         "url": "https://arxiv.org/pdf/1002.4806",
         "evidence": "The paper's Goldbach Dirichlet series has von Mangoldt weights on integer/prime-power summands and conditional continuation theorems. This is established zeta-zero context, not a theorem borrowed for the unweighted prime-only additive series."},
        {"id": "classical_prime_pair_correlation_and_uniform_sieve", "authors": "Jacob Korevaar", "year": 2008,
         "title": "Prime pairs and Zeta's zeros (preprint dated May 15, 2007)",
         "url": "https://arxiv.org/pdf/0806.0934",
         "evidence": "Reviewed equations (1.3), (1.5), (2.3): known von-Mangoldt pair correlation and an unconditional sieve upper bound uniform in the even gap. The bound supplies the r>=3 endpoint proof with the present logarithmic weights; no prime-pair conjecture or conditional zero-distribution result is imported."},
        {"id": "classical_arbitrary_interval_Brun_Titchmarsh", "authors": "Tomohiro Yamada", "year": 2023,
         "title": "Explicit improvements of Brun--Titchmarsh theorem for arbitrary intervals",
         "url": "https://arxiv.org/pdf/2312.16090",
         "evidence": "Reviewed Theorem 2; k=1 supplies the uniform O(D/log D) prime count in an interval of length D used for the r=1 gap endpoint. No improved constant or new short-interval theorem is claimed."},
        {"id": "classical_weighted_graph_Laplacian", "authors": "Kirill Krasnov and Carlos Scarinci", "year": 2013,
         "title": "Weighted Laplacians, cocycles and recursion relations",
         "url": "https://arxiv.org/pdf/1310.0653",
         "evidence": "Reviewed section 1.8 defines the known complete weighted graph Laplacian with degree diagonal and negative adjacency entries. Only this classical kernel framework is used; no physics, determinant or recursion theorem is transferred to the zeta construction."},
        {"id": "classical_binomial_difference_weights", "authors": "NIST DLMF", "year": 2026,
         "title": "Binomial theorem, equation 1.2.2",
         "url": "https://dlmf.nist.gov/1.2.E2",
         "evidence": "The recovered alternating binomial weights and multiplicative face expansion are instances of the classical finite binomial theorem. The arithmetic mask and uniform-height application do not establish a new primitive."},
        {"id": "classical_fractional_zeta_derivative", "authors": "Emanuel Guariglia", "year": 2019,
         "title": "Riemann zeta fractional derivative--functional equation and link with primes",
         "url": "https://link.springer.com/article/10.1186/s13662-019-2202-5",
         "evidence": "Equation (1.1) is N_alpha times exp(i*pi*alpha), with the construction attributed to 2015. The primary published PDF is archived; N_alpha is established prior art."},
        {"id": "closest_logarithmic_fractional_zeta_source", "authors": "Emanuel Guariglia", "year": 2024,
         "title": "Fractional calculus, Riemann zeta function and Euler products",
         "url": "https://www.sciencedirect.com/science/article/pii/S2405896324009169",
         "evidence": "The primary abstract explicitly studies a logarithmic fractional derivative. Full formulas were not retrieved; this prevents a completed compound-operator priority comparison. Abstract relevance alone does not settle operator identity."},
        {"id": "classical_uniform_rough_number_bound", "authors": "Kai (Steve) Fan and Carl Pomerance", "year": 2023,
         "title": "An inequality related to the sieve of Eratosthenes, Theorem A",
         "url": "https://math.dartmouth.edu/~carlp/erat060523rev.pdf",
         "evidence": "Theorem A states the unconditional uniform bound Phi(x,y)<x/log(y) for x>=y>=2. This existing prime-distribution theorem supplies the all-scale layer-cake moment certificate. The full imported sieve proof was not independently reverified."},
        {"id": "classical_graph_p_energy", "authors": "Francesco Tudisco and Matthias Hein", "year": 2016,
         "title": "A nodal domain theorem and a higher-order Cheeger inequality for the graph p-Laplacian",
         "url": "https://arxiv.org/abs/1602.05567",
         "evidence": "Reviewed section 2, page 3, defines the known weighted edge-difference p-energy / Rayleigh quotient. The positive-real higher moment uses that known form; no spectral or Cheeger result is imported for Riemann zeros."},
        {"id": "regular_ternary_is_different_kernel", "authors": "Jan Snellman", "year": 2026,
         "title": "Greedy Regular Convolutions, version 4 (14 August 2026)",
         "url": "https://arxiv.org/pdf/2504.02795",
         "evidence": "Equation (6) requires both exponents at a shared prime to be even. It gives delta_p times delta_p equal to zero; the global radix-three carry product gives delta_(p^2). Similar terminology is not a historical match to this kernel, and the distinction does not establish novelty."},
        {"id": "classical_Landau_factorial_ratio_floor_filters", "authors": "Jonathan W. Bober", "year": 2009,
         "title": "Factorial ratios, hypergeometric series, and a family of step functions",
         "url": "https://arxiv.org/pdf/0709.1977",
         "evidence": "Section 3 treats Landau's step-function positivity criterion; Theorem 1.2 classifies height-one integral factorial ratios. The introduction relates them to Chebyshev prime estimates. The recovered positive floor kernels are known-framework calibration, not new prime information or a new primitive."},
    ]
    registry = {
        "objective": "Find operators with independently verified signed arithmetic control of ordinary zeta across all scales, working toward RH",
        "verified_new_operators": [],
        "independent_search_stage": autonomous,
        "signed_compensator_stage": compensated,
        "signed_arithmetic_control_stage": signed_control,
        "signed_scale_polynomial_stage": stable_scale,
        "direct_signed_moment_transfer_audit": signed_mellin,
        "primary_signed_search": mellin_search,
        "signed_correlation_proof_obligations": signed_correlation,
        "signed_moment_defect_search": signed_defects,
        "rational_power_and_fractional_moment_search": fractional_moments,
        "fractional_zeta_local_branch_gate": fractional_branches,
        "imported_all_scale_signed_calibration": signed_global,
        "fractional_coefficient_and_log_kernel_search": pole_neutral,
        "general_parameter_jets_and_prime_recovery_calibration": parameter_jets,
        "signed_prime_error_filter_search": prime_error,
        "prime_density_and_signed_prime_correlation_search": prime_discrepancy,
        "fractional_prime_twist_and_signed_decay_search": prime_twists,
        "exhaustive_finite_prime_twist_coverage": prime_twist_coverage,
        "prime_oscillation_compatibility_audit": prime_oscillation,
        "fractional_arithmetic_remainder_family_search": fractional_remainders,
        "small_order_inverse_Mertens_compatibility_audit": mertens_limits,
        "complete_tail_Mellin_kernel_frontier_search": mellin_kernels,
        "complete_tail_fresh_parameter_observer_diagnostic": kernel_observers,
        "complete_signed_Gram_and_squarefree_density_search": kernel_correlations,
        "typed_lattice_global_estimate_synthesis_and_fractional_banks": lattice_synthesis,
        "normalized_root_arithmetic_and_signed_profile_learning": root_lattices,
        "divisor_preconditioning_with_retained_signed_arithmetic": divisor_preconditioners,
        "complete_fractional_centers_and_signed_cofinal_parameter_families": branch_centers,
        "unbounded_rational_fractional_evaluation_contracts": rational_fractional_contracts,
        "critical_signed_energy_defect_and_explicit_dense_residual": critical_defects,
        "divisor_dual_full_defect_candidates_and_frozen_proof_queue": divisor_duals,
        "separate_analytical_review_of_detector_candidates": dual_analytical_review,
        "independent_constant_profiles_and_actual_signed_nullspace_gap": signed_gap_profiles,
        "cofinal_actual_arithmetic_counterexamples_to_fitted_gap_candidates": signed_gap_cofinal,
        "parallel_Sol_6_1_analytical_candidate_reviews": candidate_reviews,
        "response_inferred_inverse_prefix_operators_and_signed_scale_potentials": inverse_prefix,
        "parallel_Sol_6_1_inverse_prefix_bounds_and_stored_fit_refutations": inverse_prefix_reviews,
        "workflow_reliability_and_generic_signed_bound_discovery_audit": workflow_audit,
        "typed_signed_arithmetic_and_complete_scale_stencils": signed_arithmetic,
        "parallel_signed_arithmetic_reviews_and_dense_residual_reduction": signed_arithmetic_reviews,
        "uniform_RH_sufficient_signed_controls_verified": (
            mellin_search["uniform_sublinear_signed_controls_verified"] +
            signed_defects["uniform_sublinear_signed_controls_verified"] +
            fractional_moments["uniform_sublinear_signed_controls_verified"] +
            pole_neutral["uniform_RH_sufficient_signed_controls_verified"] +
            parameter_jets["uniform_RH_sufficient_signed_controls_verified"] +
            prime_error["uniform_RH_sufficient_signed_controls_verified"] +
            prime_discrepancy["uniform_RH_sufficient_signed_controls_verified"] +
            prime_twists["uniform_RH_sufficient_signed_controls_verified"] +
            prime_oscillation["uniform_RH_sufficient_signed_controls_verified"] +
            fractional_remainders["uniform_RH_sufficient_signed_controls_verified"] +
            mertens_limits["uniform_RH_sufficient_signed_controls_verified"] +
            mellin_kernels.get("uniform_RH_sufficient_signed_controls_verified", []) +
            kernel_correlations.get("uniform_RH_sufficient_signed_controls_verified", []) +
            lattice_synthesis.get("uniform_RH_sufficient_signed_controls_verified", []) +
            root_lattices.get("uniform_RH_sufficient_signed_controls_verified", []) +
            divisor_preconditioners.get("uniform_RH_sufficient_signed_controls_verified", []) +
            branch_centers.get("uniform_RH_sufficient_signed_controls_verified", []) +
            critical_defects.get("uniform_RH_sufficient_signed_controls_verified", []) +
            divisor_duals.get("uniform_RH_sufficient_signed_controls_verified", []) +
            dual_analytical_review.get("uniform_RH_sufficient_signed_controls_verified", []) +
            signed_gap_profiles.get("uniform_RH_sufficient_signed_controls_verified", []) +
            signed_gap_cofinal.get("uniform_RH_sufficient_signed_controls_verified", []) +
            candidate_reviews.get("uniform_RH_sufficient_signed_controls_verified", []) +
            inverse_prefix.get("uniform_RH_sufficient_signed_controls_verified", []) +
            inverse_prefix_reviews.get("uniform_RH_sufficient_signed_controls_verified", []) +
            workflow_audit.get("uniform_RH_sufficient_signed_controls_verified", [])),
        "later_analytic_obstructions_supersede_archived_plausibility_counts": True,
        "additional_signed_estimate_forms": [
            "For every cofinal positive epsilon, a finite scale-independent B_epsilon with A_2(2X)-4*A_2(X)<=B_epsilon*X^(2+epsilon) at every dyadic X suffices for RH with unfiltered actual Mertens recovery",
            "A_q(2X)-rho*A_q(X)<=B X^gamma at every dyadic scale; rho<=2^(q/2+1) and gamma<=q/2+1 suffice for RH with an all-height zero bridge",
            "A fixed moment order with a logarithmic loss is allowed; exact fitted finite constants are not mandatory",
            "General rational effective moments q>=1 use Holder-Mellin; 0<q<1 uses an explicit Lipschitz-to-L1 transfer",
            "Signed roots require inverse and effective-order recovery; principal complex roots retain branch conditions and zero monodromy",
            "Coupled signed bounds |G_a(x)-1|<=C*a*sqrt(x)*(1+log x)^L for every x>=2 and every 0<a<=a0 would control actual prime-power error and suffice for RH",
            "Signed first-jet prime-error dilation bounds C*n^theta*log(e+n)^ell at every integer n extend to all real scales with bounded jump costs; theta<=1/2 suffices for RH without an all-height multiplier nonvanishing premise",
            "Actual-prime factorial/floor certificates prove psi(x)<=C*x and a logarithmic Gram diagonal saving; a uniform C_off(X)<=rho*D(X)+B*X^gamma for matched prime error, rho>-1 and gamma<=2, would suffice for RH",
            "Fractional arithmetic twists allow negative signed decay with exact Mellin centers; max(theta,-increment_shift)+leading_shift<=1/2 suffices for RH through the finite right-shift multiplicity chain",
            "Pure critical-power Lambda-channel bounds are ruled out by an imported oscillation theorem and generic Stieltjes inversion; positive rational log losses remain eligible",
            "Signed fractional discrete/continuous families at a_q=1/(max(1,D)*q) recover all ordinary zeros through an exact parameter pole; a square-root bound for EVERY n and EVERY q would suffice for RH, including high-pass families with vanishing small-order limits",
            "Common pure square-root family bounds also control their exact small-order limit; the charged Volterra inverse must respect named Mertens extremum lower bounds, while positive logarithmic losses remain eligible",
            "Complete inverse-kernel Gram observables retain signed cross terms; positive or singular recovering metrics with cofinal point exponent 1/2 suffice for RH, charging all positive pivots",
            "Squarefree density corrections have a proved all-real-scale square-root bound; a cofinal quarter-power bound with a certified density multiplier suffices for RH through multiplicity, reflection and height halving",
        ],
        "historical_priority_is_acceptance_gate": False,
        "uniform_sublinear_signed_controls_verified": (
            mellin_search["uniform_sublinear_signed_controls_verified"] +
            signed_defects["uniform_sublinear_signed_controls_verified"] +
            fractional_moments["uniform_sublinear_signed_controls_verified"]),
        "legacy_uniform_sublinear_field_scope": "RH-strength detector estimates; weaker imported signed control and actual-prime harmonic/tail calibrations are reported separately",
        "primary_research_focus": "Prove uniform signed moments, arithmetic pair bounds, prime-error decay or centered squarefree quarter-power bounds, prioritizing actual arithmetic and fully charged ordinary-zeta recovery",
        "RH_sufficient_single_moment_target": "For some fixed rational q>=1, prove integral_X^(2X)|R(t)|^q dt <= C X^(q/2+1) at every dyadic X>=1 with an all-height nonzero multiplier",
        "primary_next_actions": [
            "Use learned signed residuals to infer all-scale moment, correlation or defect estimates, charging the costs required by the chosen ordinary-zeta bridge",
            "Search for and independently verify an arithmetic proof of those estimates; finite extrapolations remain conjectural",
            "Retain unsupported creative operators while proving their ordinary-zeta bridge separately",
            "Accept RH only after a proved uniform signed estimate excludes every ordinary zero right of the critical line",
        ],
        "prime_information_search_priority": prime_scale["prime_information_priority"],
        "prime_information_current_status": "Exact extraction, residue/window observables and all-scale positive floor traces are verified calibrations. The factorial trace and prime-density certificate also give signed actual-prime harmonic and reciprocal-tail bounds at every scale, with ordinary-zeta recovery exponent one. An RH-strength uniform signed prime-specific estimate remains missing.",
        "creative_grammar_expansion": {
            "productions": creative["production_catalogue"],
            "search": {"operator_programs": creative["operator_word_search"]["map_programs_evaluated"],
                       "distinct_training_fingerprints": creative["operator_word_search"]["distinct_training_fingerprints"],
                       "rewrite_proved_aliases": creative["operator_word_search"]["universal_rewrite_certified_aliases"],
                       "numerical_aliases_still_unproved": creative["operator_word_search"]["unproved_training_aliases"],
                       "phase_products": creative["nonassociative_phase_search"]["phase_product_programs"],
                       "unknown_kernel_coefficients": creative["learned_phase_kernel_search"]["unknown_coefficients"],
                       "learned_universal_kernel_span_dimension": creative["learned_phase_kernel_search"]["universal_kernel_span_dimension"],
                       "small_characteristic_false_laws_rejected": len(creative["learned_phase_kernel_search"]["cross_prime_false_law_controls"])},
            "proved_calibration_laws": ["K=F^*INV MASK F is Hermitian with K^2=I-J/p, K^3=K and norm one, for every prime",
                                       "The phase product exp(2*pi*i*x*y^2/p) has graded associator exp(-4*pi*i*x*y*z/p), with an all-integer Omega lift",
                                       "Four learned degree-five polynomial cocycle kernels have identically zero associator",
                                       "[F,MASK] has rank two for every prime; rank[F,INV]=p-3 for every odd prime by multiplicative-character diagonalization"],
            "ordinary_zeta_zero_fidelity_after_residue_embedding_proved": False,
            "new_all_scale_prime_information_estimate_proved": False,
            "generic_basis_transport_and_automatic_Gram_positivity_count_as_information_gain": False,
            "mathematical_independent_checks_passed": creative_check["all_passed"],
            "public_entry_point_audit": creative_check["public_entry_point_audit"],
            "discovery_is_prior_free": False,
            "bias_scope": "Typed primitives, word depth and polynomial feature degree constrain the search; finite coincidences are not proofs",
            "proof": "creative_grammar_proof.txt",
            "data": ["creative-results/creative_search.json", "creative-results/creative_verification.json"],
            "counts_as_new_operator": False,
            "included_in_ordinary_zeta_family_consequence_or_full_comparison_counts": False,
        },
        "external_proof_calibrations": [{
            "id": "OpenAI_QRH_finite_arithmetic_spine",
            "source_commit": qrh["source_commit"],
            "recovered_scalar_conversion": qrh["Gauss_conversion_recovery"],
            "finite_Fourier_and_nonunit_mask_controls": qrh["character_Fourier_and_mask_controls"],
            "cube_completion_inverse_control": qrh["cube_completion_inverse_control"],
            "prime_compensation_control": qrh["prime_compensation_control"],
            "independent_checks": qrh_check["checks"],
            "full_theta_reflection_implemented": False,
            "global_mean_square_bounds_independently_verified": False,
            "entire_QRH_proof_independently_verified": False,
            "comparison_to_ordinary_RH": "The cited zero-free regions remain weaker than the critical-line conclusion. This detector's finite calibrations verify no new zero-free region.",
            "proof": "creative_grammar_proof.txt section 5",
            "review": "qrh_operator_review.txt",
            "data": ["qrh-results/qrh_operator_benchmark.json", "qrh-results/qrh_operator_verification.json"],
            "counts_as_new_operator": False,
            "included_in_ordinary_zeta_family_consequence_or_full_comparison_counts": False,
        }],
        "creative_spectral_leads": [{
            "id": "Fourier_residue_inversion_commutator_rank",
            "term": creative["commutator_defect_search"]["observed_lead"]["term"],
            "sampled_prime_count": len(creative["commutator_defect_search"]["records"]),
            "sampled_rank_rule": "p-3",
            "proved_universal_law": "rank[F,INV]=p-3 for every odd prime by classical cyclotomic independence",
            "universal_rank_equality_proved": True,
            "uniform_nonzero_singular_value_bound_proved": False,
            "ordinary_zeta_zero_bridge_proved": False,
            "new_prime_information_estimate_proved": False,
            "historical_novelty_established": False,
            "priority": "Supporting algebraic lead; no promotion ahead of new all-scale prime-information estimates",
            "data": "creative-results/creative_search.json",
            "counts_as_new_operator": False,
        }],
        "creative_search_next_targets": [
            "Invent and test prime-mark/scale compensation on complete arithmetic families; prove a uniform energy or cancellation estimate beyond identity rearrangement",
            "Retain an explicit bridge to ordinary-zeta zero or pole information when an operator is claimed to address RH",
            "Search kernel coefficients and representations while allowing defects, projections, nonassociativity and anti-linear maps",
            "Measure nonzero character eigenvalues and arithmetic content before pursuing a spectral RH interpretation of the proved rank law",
        ],
        "global_moment_inequality_grammar": {
            "productions": global_moment["production_catalogue"],
            "anti_overfit_protocol": global_moment["anti_overfit_protocol"],
            "operator_programs_scored": 48,
            "universally_certified_transfers": 24,
            "finite_training_recurrences_rejected": 16,
            "learned_positive_functionals": global_moment["positive_functional_search"],
            "moment_to_arithmetic_target_transfer": global_moment["moment_to_arithmetic_target_transfer"],
            "proved_global_calibrations": [
                "Additive-twist M2<=H*ceil(D/H)*sum|a|^2 for all integer scales D,H; nonlinear index kernels have separate prime-field root-count certificates",
                "Signed recursive polynomial fourth moment (4*4^j-(-2)^j)/3<=3/2*N^2 for every level j, N=2^j",
                "Lacunary ternary-digit polynomial fourth moment 6^j for every level j",
                "Persistent forcing has uniform normalized cost only with strict contraction; critical resonance introduces a logarithmic scale loss",
            ],
            "independent_verification_passed": global_moment_check["all_passed"],
            "complete_actual_zeta_inverse_family_observations": len(global_moment["additive_arithmetic_energy_search"]["actual_zeta_inverse_family_observations"]),
            "new_arithmetic_cancellation_bound_for_Mobius_or_prime_families_proved": False,
            "ordinary_zeta_zero_bridge_proved": False,
            "QRH_global_moment_bound_independently_verified": False,
            "next_target": "Invent certified global moment, admissible actual-prime row-count and row-error estimates for the same target family; control all scale costs and a nonvanishing ordinary-zeta Mellin numerator",
            "proof": "global_moment_proof.txt",
            "data": ["global-moment-results/global_moment_search.json", "global-moment-results/global_moment_verification.json"],
            "counts_as_new_operator": False,
            "included_in_ordinary_zeta_family_consequence_or_full_comparison_counts": False,
        },
        "fractional_prime_decoder_lead": {
            "id": fractional["candidate_id"],
            "status": "verified_formal_arithmetic_family_and_two_local_ordinary_zero_bridges_novelty_unresolved",
            "definition": fractional["definition"],
            "domain": fractional["domain"],
            "production_catalogue": fractional["production_catalogue"],
            "public_program_examples": fractional["public_program_examples"],
            "prime_value": 1,
            "sharp_composite_magnitude_upper_bound": fractional["prime_indicator_sup_error_bound"],
            "strict_sign_law": "(-1)^(omega(n)+omega(gcd_prime_exponents(n))-1)",
            "universal_triangular_inverse_proved": True,
            "ordinary_input_root_commutation": "rejected at squarefree n=6 for alpha=beta=1/2",
            "uniform_prime_indicator_coefficient_limit": "alpha tends to one from below",
            "coefficient_API_independent_gates": len(fractional_check["checks"]),
            "analytic_independent_gates": len(fractional_analytic_check["checks"]),
            "public_entry_point_audit": fractional_check["public_entry_point_audit"],
            "actual_zero_controls": fractional_analytic_check["actual_zero_and_corridor_audit"],
            "six_complete_native_comparisons_evaluate": "unnormalized L_(1/2), not the complete normalized B_(1/2)",
            "full_normalized_B_native_value_compared": False,
            "global_numerator_nonvanishing_at_every_zeta_zero_proved": False,
            "new_uniform_prime_distribution_estimate_proved": False,
            "new_RH_estimate_proved": False,
            "historical_novelty_established": False,
            "closest_full_prior_art_formula_comparison_completed": False,
            "proof": "fractional_prime_proof.txt",
            "prior_art_audit": "fractional_prior_art_audit.txt",
            "data": ["fractional-prime-results/fractional_prime_search.json", "fractional-prime-results/fractional_prime_verification.json",
                     "fractional-prime-results/fractional_prime_analytic.json", "fractional-prime-results/fractional_prime_analytic_verification.json"],
            "included_in_main_family_consequence_or_comparison_counts": False,
            "counts_as_historically_new_operator": False,
        },
        "actual_prime_moment_count_bridge": {
            "generic_affine_transfers": prime_moment["generic_affine_moment_search"],
            "definition": "M_(2k)=sum w_n*|B_alpha(n)|^(2k), with nonnegative weights and total W",
            "universal_count_transfer": prime_moment["uniform_transfer"],
            "all_scale_scope": "Every finite weighted window or residue set; actual moment enclosures and the score gap require separate certificates",
            "minimum_order_compiler": "Choose k with (epsilon+delta^(2k)*W)/(1-delta^(2k)) < target_width, retaining scale dependence",
            "Fourier_family_bridge": prime_moment["complete_Fourier_second_moment_bridge"],
            "ordinary_circle_even_moment_substitution_rejected": True,
            "finite_arithmetic_groups": len(prime_moment["actual_arithmetic_moment_count_bridge"]["records"]),
            "unique_integer_counts_verified": sum(r["unique_integer_count_certified"] for r in prime_moment_check["arithmetic_audit"]["records"]),
            "independent_audit_gates": len(prime_moment_check["checks"]),
            "public_entry_point_audit": prime_moment_check["public_entry_point_audit"],
            "separate_all_scale_energy_estimate_supplied": True,
            "all_scale_energy_estimate_domain": prime_moment["all_scale_energy_estimate_domain"],
            "known_sieve_all_scale_moment_certificate": prime_moment["prime_roughness_and_all_scale_moment_certificate"],
            "new_independent_prime_distribution_estimate_supplied": False,
            "new_uniform_prime_distribution_estimate_proved": False,
            "ordinary_zeta_zero_bridge_for_moment_operators_proved": False,
            "historical_novelty_established": False,
            "proof": "prime_moment_transfer_proof.txt",
            "all_scale_energy_proof": "prime_roughness_moment_proof.txt",
            "data": ["prime-moment-results/prime_moment_transfer.json", "prime-moment-results/prime_moment_verification.json"],
            "included_in_main_family_consequence_or_comparison_counts": False,
            "counts_as_historically_new_operator": False,
            "next_target": "Discover a stronger arithmetic bound, main term or cancellation transfer beyond the classical rough-number envelope, with a separate ordinary-zero bridge",
        },
        "unequal_shift_prime_decoder_lead": {
            "id": shift_ratio["candidate_id"],
            "status": "verified_arithmetic_family_full_native_decoder_and_zero_sensitive_RH_equivalence_novelty_unresolved",
            "definition": shift_ratio["definition"],
            "production_catalogue": shift_ratio["production_catalogue"],
            "public_program_examples": shift_ratio["public_program_examples"],
            "sharp_prime_gap": "B_v(p)=1, every composite has modulus <=(1-v)/(1+v), 0<v<1",
            "least_prime_envelope": "t/(v+(1-v)*g*t), t=log P^-(n)/log n, g=gcd prime exponents",
            "sieve_imported_all_scale_M2": "sum_[X,2X]|B_v(n)|^2 <=2*(1+v)/v * X/log X",
            "unknown_fractional_numerator_nonvanishing_required": False,
            "all_zero_orders_local_signature": "zero order m gives coefficient m/v^m in the local logarithm, with a zero-free right corridor",
            "pole_regularized_RH_equivalence": "B_v(s)+v*(1/zeta)'(v+(1-v)*s)*log(s-1) has single-valued holomorphic continuation to Re(s)>1/2 iff RH",
            "positive_finite_mixture_RH_equivalence": "The same criterion holds after summing regularizers with arbitrary positive rational weights of exact total one",
            "fractional_relation": "B_alpha is a Beta(alpha,1-alpha) positive mixture of B_v",
            "known_integer_logarithm_closure": shift_ratio_check["known_integer_logarithm_closure_audit"],
            "finite_positive_mixture_controls": shift_ratio_check["public_entry_point_audit"]["held_out_positive_mixture_records"],
            "coefficient_API_independent_gates": len(shift_ratio_check["checks"]),
            "analytic_independent_gates": len(shift_ratio_analytic_check["checks"]),
            "public_entry_point_audit": shift_ratio_check["public_entry_point_audit"],
            "complete_B_native_comparisons": 6,
            "actual_zero_controls": shift_ratio_analytic_check["actual_zero_and_corridor_audit"],
            "new_independent_prime_distribution_estimate_proved": False,
            "new_RH_estimate_proved": False,
            "historical_novelty_established": False,
            "proof": "shift_ratio_proof.txt",
            "prior_art_audit": "shift_ratio_prior_art_audit.txt",
            "scientific_figure": ["shift-ratio-results/shift_ratio_overview.png", "shift-ratio-results/shift_ratio_overview.pdf"],
            "data": ["shift-ratio-results/shift_ratio_search.json", "shift-ratio-results/shift_ratio_verification.json",
                     "shift-ratio-results/shift_ratio_analytic.json", "shift-ratio-results/shift_ratio_analytic_verification.json"],
            "included_in_main_family_consequence_or_comparison_counts": False,
            "counts_as_historically_new_operator": False,
            "next_target": "Audit exact historical constructions and seek a uniform cancellation or continuation estimate beyond the known-sieve coefficient energy bound",
        },
        "estimate_discovery_stage": {
            "status": "bounded_certificate_search_for_estimates_implemented_no_new_RH_bound",
            "production_catalogue": estimates["production_catalogue"],
            "arithmetic_cutoff": estimates["coefficient_cutoff"],
            "kernel_programs_generated_before_observations": 20,
            "growth_bounds_proposed": 700,
            "status_counts": estimates["cancellation_estimate_search"]["status_counts"],
            "independent_estimate_and_arithmetic_audit": estimates_check["arithmetic_and_fit_audit"],
            "known_zero_false_bound_control": estimates["cancellation_estimate_search"]["finite_survivor_but_mathematically_impossible_control"],
            "automatically_learned_classical_cancellation_bound": estimates["learned_cancellation_certificates"]["best_linear_bound"],
            "automatically_synthesized_positive_moment_certificates": 12,
            "strict_improvements_over_supplied_mixture_Jensen_bounds": [
                {key: row[key] for key in ("mixture", "moment_order", "constant_expression", "constant_approximation", "existing_Jensen_constant")}
                for row in estimates["positive_energy_estimate_search"]["records"]
                if row.get("strictly_improves_Jensen_for_this_mixture")],
            "external_full_sieve_proof_independently_verified": False,
            "RH_relevance": "Nonvanishing Mellin kernels turn a proved all-scale square-root signed Mobius bound with finite logarithmic cost into a sufficient RH criterion; that cancellation certificate is missing",
            "new_independent_prime_distribution_estimate_proved": False,
            "new_RH_estimate_proved": False,
            "independent_audit_gates": 6,
            "public_entry_point_audit": estimates_check["public_entry_point_audit"],
            "proof": "estimate_proof.txt",
            "data": ["estimate-results/estimate_search.json", "estimate-results/estimate_verification.json"],
            "scientific_figure": ["estimate-results/estimate_search_overview.png", "estimate-results/estimate_search_overview.pdf"],
            "included_in_main_family_consequence_or_comparison_counts": False,
            "counts_as_historically_new_operator": False,
            "next_target": "Extend signed decomposition and multiscale recurrence proof search to discharge the recorded uniform cancellation obligations",
        },
        "estimate_certificate_feedback": {
            "production_catalogue": estimate_feedback["production_catalogue"],
            "learned_prime_pool": estimate_feedback["learned_prime_pool"],
            "conditioning_sets": estimate_feedback["prime_sets_searched"],
            "proved_affine_bounds": 280,
            "feedback_status_counts": estimate_feedback["feedback_status_counts"],
            "repaired_all_scale_estimates_proved": estimate_feedback["repaired_all_scale_estimates_proved"],
            "independent_estimate_feedback_audit": estimate_feedback_check["estimate_feedback_audit"],
            "target_preserving_rewrite": "S_W(X)=sum_(gcd(n,P)=1)mu(n)*sum_(d|P)mu(d)*W(d*n/X)",
            "classical_smoothing_calibration": "|sum_(n<=X)mu(n)(1-n/X)|<=X/8+1 for every real X>=1",
            "all_scale_proof_method": "Positive piecewise Bernstein envelope, elementary finite-sieve discrepancy, exact initial-scale checks and a monotone tail bound",
            "external_prime_distribution_theorem_used": False,
            "sublinear_cancellation_certificate_discovered": False,
            "new_RH_estimate_proved": False,
            "new_independent_prime_distribution_estimate_proved": False,
            "independent_audit_gates": 5,
            "proof": "cancellation_rewrite_proof.txt",
            "data": ["estimate-results/cancellation_rewrite_search.json", "estimate-results/cancellation_rewrite_verification.json"],
            "included_in_main_family_consequence_or_comparison_counts": False,
            "counts_as_historically_new_operator": False,
            "next_target": "Learn a certificate for the remaining signed coprime-row cancellation goals at sublinear growth while preserving the original Mellin transform",
        },
        "status": "Research active toward RH: signed operator and transport properties are verified in their stated domains; the required uniform signed arithmetic estimates remain unproved. Historical priority is not an acceptance gate.",
        "mathematically_verified_nonlinear_candidates": ["primewise_log_exp_root_limit", "global_degree_log_exp_root_limit", "prime_binary_partition_regularizer", "quadratic_index_difference_root_transfer", "nonlinear_prime_sum_log_coupling"],
        "mathematically_verified_linear_candidates": ["canonical_prime_degree_projection", "prime_sum_sector_decoder", "residue_visible_prime_power_product_decoder"],
        "mathematically_verified_integer_order_candidates": ["floor_size_root_limit_transfer", "ceiling_size_root_limit_transfer"],
        "integer_order_individual_analytic_domain": "Absolute convergence and locally uniform zeta root-limit convergence on Re(s)>1; the finite-power holomorphic RH gate is rejected; other continuations unestablished",
        "integer_order_individual_RH_holomorphy_gate": "Rejected: finite-q lifts have artificial singularities on Re(s)=1; U cannot be made holomorphic at s=1 by any finite real power of s-1",
        "rejected_individual_RH_regular_size_transfer_candidates": ["floor_size_root_limit_transfer", "ceiling_size_root_limit_transfer"],
        "verified_known_kernel_closures": ["Boolean_intersection_of_two_floor_size_products", "prime_pair_product_and_additive_convolution_calibration", "harmonic_Stirling_log_square_and_root_of_unity_filters", "gap_prime_pair_bilinear_correlation_and_log_exp_transform", "prime_gap_Laplacian_logarithmic_shear", "higher_prime_moment_shear_uniform_height_limit", "global_radix_degree_carry_log_exp_transfer", "Landau_floor_prime_trace_and_Mobius_scale_decoder"],
        "joint_floor_size_finite_root_domain_gate": "For multiplicatively independent bases and every finite q>=2, Re(s)=1 is a natural boundary; these unmodified lifts cannot cross into the critical strip",
        "constant_signed_orientation_cancellation_gate": "Among nonzero rational constant combinations for independent bases, all nonconstant Abelian modes cancel only for equal weights at q=2; every such combination at q>=3 has a natural boundary on Re(s)=1",
        "corrected_square_root_cancellation_status": "Verified arithmetic reduction to known paired-root/projection compositions, with a nonzero correction on Re(s)>0 and a dyadic RH-equivalent root criterion; not a new primitive or RH estimate",
        "mixed_index_root_gate": "The selected factorial-normalized subset transfer converges on Re(s)>0, but its B roots differ from ordinary Dirichlet roots and are holomorphic across actual simple zeta zeros; its regularity alone is not an RH diagnostic",
        "quadratic_difference_root_gate": "Ordinary D roots preserved; H_beta=zeta^beta*exp(beta*Delta), with zero-free correction on Re(s)>-m+(m+1)/2^k. The negative domain is grouped analytic continuation, not ordinary coefficient-series convergence.",
        "nonlinear_pair_root_gate": "Universal input-root commutation is rejected, but both zeta root families have holomorphic nonzero corrections on Re(s)>2/5 for r=3; input amplitude beta^2 differs from output amplitude beta. Ordinary zeta zeros and root monodromy are retained.",
        "universal_input_root_constraint_audit": "For coefficient-local polynomial maps, universal half-root commutation forces EXP_D L LOG_D with linear L. The grammar now also allows nonlinear log couplings with separately proved ordinary-zeta root bridges.",
        "prime_sum_decoder_root_gate": "A universal prime-power sector decoder recovers a squared-log zeta obstruction from the holomorphic encoded correction. This is an unbounded operation at the same Dirichlet weight; pure power weights that make it bounded at the critical line shift the obstruction left.",
        "full_prime_pair_extension_gate": "All prime-pair images, including diagonals, have unique complete prime-power fibres. Product decoding recovers P(s)^2 with ordinary-zeta logarithmic branching; sum decoding recovers classical ordered Goldbach counts, with no critical-strip continuation established here. Its sharp Hilbert threshold is tau>=(r+2)*sigma+1/2.",
        "residue_visible_decoder_root_gate": "The linear aggregator restores admissible same-prime pairs and yields U_r=(LOG zeta(s)-LOG zeta(rs)/r)^2+R_r, with R_r holomorphic on Re(s)>1/r. Actual-zero branching and a quantitative parameter-limit anomaly are retained. Sharp decoder domain loss still prevents transfer to the critical line.",
        "full_prime_power_endpoint_refinement": "The full encoded source has exact absolute abscissa 2/(r+2), with endpoint convergence by weighted prime-power PNT. Its endpoint norms are uniformly bounded for r>=3, but norm-one decoded targets are 2(r+1)/(r+2), at least 8/5. Earlier strict thresholds used only the then-available open-half-plane certificate.",
        "gap_correlation_root_gate": "For the difference index ab|a-b|^r, the exact correction abscissa is max(2/(r+2),1/2). The endpoint diverges for r=2 and converges for r=1 and r>=3. At r=3 the exponential factor is holomorphic on Re(s)>1/2 and continuous, finite and nonzero on the critical line; ordinary-root behavior is retained from the right. Whole critical-zero disk holomorphy and an RH estimate are unproved.",
        "prime_gap_Laplacian_root_gate": "The prime-only diagonal completion gives an exact logarithmic parameter group and closed inverse. Its paired correction is holomorphic on Re(s)>1/3 at r=4, while ordinary correction coefficients have absolute edge 1/2. Whole actual-zero disks have bounded, nonzero exponential factors and ordinary zeta root exponents persist. Hermitian positivity is a separate nonholomorphic form, not an RH spectral theorem.",
        "higher_prime_moment_root_gate": "Even moment degree m with gap power m+2 and gap>=2 has paired correction domain Re(s)>1/(m+1), ordinary correction convergence Re(s)>1/m, and a height-uniform critical-half-plane correction bound C*rho^(m-4), rho=1/sqrt(6)+1/sqrt(10)<1. Whole zero disks retain multiplicity*beta and input amplitude beta^2 regardless of m. The unmasked coefficientwise identity limit has a certified divergent scalar counterexample. The root-continuation RH criterion remains unproved.",
        "global_radix_root_gate": "For b>=3, 0<beta<=1, the degree-(b-1) LOG-zeta polynomial has nonzero leading H=F_(b,beta/b)(b*s) at every height in Re(s)>=1/2. Complete branch differences detect ordinary zeta zeros. Typed roots do not preserve ordinary output-root locations: radix three has a certified simple operator zero where zeta and the transferred input half-root are nonzero. A single pointwise loop jump can vanish. The polynomial pole-corrected RH-equivalent continuation is unproved.",
        "prime_scale_root_gate": "For balanced floor filters, Mellin(T_c)=-zeta_prime(s)*A_c(s)/s is regular at every zeta zero, so its unmodified holomorphy is not an RH test. Mobius decoding gives Mellin(I_c)=-zeta_prime(s)/zeta(s)*A_c(s)/s. The central symbol 2**s-2 is nonzero in Re(s)<1, preserving nontrivial-zero poles. No all-X critical-scale bound on the decoded contrast is proved.",
        "verified_arithmetic_consequences": [{
            "id": "dyadic_extraction_and_real_root_parameter",
            "parent_candidate": "primewise_log_exp_root_limit",
            "definition": "T_beta(f)=EXP_infinitary(beta*LOG_Dirichlet(f)); E_m(f)(n)=f(n^m)",
            "laws": ["E_m preserves infinitary convolution on all inputs iff m is a power of 2",
                     "T_beta(u)(n^(2^k))=T_(beta/2^k)(u)(n), for all n,k and parameters beta",
                     "For every real beta in [0,1], H_beta=zeta^beta*R_beta initially Re(s)>1, with R_beta holomorphic and nonzero on Re(s)>1/2",
                     "RH iff every pole-cancelled dyadic root transfer admits single-valued holomorphic continuation to Re(s)>1/2"],
            "verification": {"models_scored": dyadic["search"]["models_scored"],
                             "training_fits": dyadic["search"]["training_fits"],
                             "fresh_surviving_multipliers": [x["multiplier"] for x in dyadic["search"]["survivors"]],
                             "independent_exact_verifier_passed": dyadic_check["all_passed"],
                             "continuous_parameter_zero_free_bound": dyadic["uniform_real_parameter_certificate"]["total_bound"],
                             "actual_zeta_ball_checks": len(dyadic_analytic["actual_zeta_ball_checks"]),
                             "multiplicity_controls_passed": dyadic_analytic["multiplicity_and_branch_control"]["all_passed"],
                             "actual_simple_zeta_zero_Rouche_and_root_control_passed": dyadic_analytic["actual_critical_line_zero_control"]["all_passed"],
                             "actual_zeta_power_arithmetic_control_cases": len(dyadic_analytic["actual_critical_line_zero_control"]["actual_zeta_power_arithmetic_controls"])},
            "proof": "dyadic_root_proof.txt", "data": ["dyadic-results/dyadic_root_search.json", "dyadic-results/dyadic_root_verification.json", "dyadic-results/dyadic_analytic_probe.json"],
            "historical_status": "Known primitives and binary shifting framework; precise application not matched to a reviewed publication. Historical novelty remains unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "carry_projection_factorization_and_prime_hierarchy",
            "parent_candidate": "canonical_prime_degree_projection",
            "definition": "P_b(f)=EXP_Dirichlet(M_b(LOG_Dirichlet(f)))",
            "laws": ["P_b is an idempotent ordinary unit-group homomorphism; all prime-base projections commute",
                     "M(T(f))=S(P_2(f)) on every normalized input",
                     "S(f)=M(T(f)) iff M(LOG_Dirichlet(f))=LOG_Dirichlet(f)",
                     "All prime-base projections converge coefficientwise to classical multiplicative completion"],
            "verification": {"independent_exact_checks_passed": projection_check["all_passed"],
                             "finite_bases_false_completion_counterexample_n": 3072},
            "proof": "projection_proof.txt sections 4 and 5", "counts_as_separate_new_operator": False,
        }, {
            "id": "cubic_transfer_commutator",
            "parent_candidates": ["primewise_log_exp_root_limit", "global_degree_log_exp_root_limit"],
            "law": "(T S f-S T f)(p^2*q)=f(p)^2*f(q), distinct primes p,q",
            "support_law": "The commutator vanishes at prime powers and squarefree indices for every normalized input",
            "verification": {"polynomial_programs_scored": projection["commutator_search"]["monomials_scored"],
                             "independent_symbolic_identity_passed": projection_check["checks"]["symbolic_cubic_commutator_identity_proved"]},
            "analytic_limit": "Composed zeta-input series converge on Re(s)>=2; a full Re(s)>1/2 bridge is unestablished",
            "proof": "projection_proof.txt section 6", "counts_as_separate_new_operator": False,
        }, {
            "id": "suspension_module_and_factorial_commutator_family",
            "parent_candidates": ["primewise_log_exp_root_limit", "global_degree_log_exp_root_limit"],
            "laws": ["For F=F_0+y F_1 with y^2=0, T(F)=t+y(t A k), S(F)=t+y B(t,k), t=EXP_A(log F_0), k=F_1/F_0",
                     "B(t,k)_e=sum_(a+b=e) 1[a&(b+1)=0]*t_a*k_b; B is a unital left A-module action, not a commutative product",
                     "(T S-S T)(u^{*alpha})(p^2*q_1*...*q_k)=(-1)^(k+1)*k!/2*alpha^(k+2), for k>=2 and distinct primes",
                     "At k=1 the correct coefficient is alpha^3, twice the extrapolated factorial value"],
            "verification": {"factorial_programs_scored": coupling["factorial_grammar"]["programs_scored"],
                             "training_fits": len(coupling["factorial_grammar"]["training_fits"]),
                             "equivalent_survivors": len(coupling["factorial_grammar"]["survivors"]),
                             "fresh_other_prime_arity_cutoff": 16,
                             "independent_tensor_coefficients": coupling_check["tensor_coefficients_independently_compared"],
                             "exact_audit_passed": coupling_check["all_passed"]},
            "proof": "coupling_proof.txt sections 1 through 4",
            "historical_status": "Known primitives and labelled formal combinatorics; exact compound law not matched to reviewed prior art. Historical originality remains unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "first_other_prime_commutator_sector_analytic_bridge",
            "parent_candidates": ["primewise_log_exp_root_limit", "global_degree_log_exp_root_limit"],
            "definition": "d_e=(T S u-S T u)(p^e*q), C_1=sum_(p!=q,e>=2) d_e*(p^e*q)^(-s)",
            "laws": ["C_1=A*P-B=A*log(zeta)-A*Q-B on Re(s)>1; A,B,Q holomorphic on Re(s)>1/2",
                     "RH iff C_1+A*log(s-1) continues holomorphically and single-valuedly to Re(s)>1/2"],
            "verification": {"local_exact_degree": coupling_check["local_degree_independently_compared"],
                             "weighted_norm_radius": coupling["local_norm_certificate"]["radius"],
                             "fresh_actual_zeta_points": len(coupling_analytic["actual_zeta_ball_checks"]),
                             "independent_analytic_audit_passed": coupling_analytic_check["all_passed"],
                             "actual_simple_zero_monodromy_certified": coupling_analytic["actual_critical_line_zero_control"]["all_passed"]},
            "analytic_limits": ["Full commutator half-plane continuation remains unestablished",
                                "The selected sector reduces to scalar prime-zeta sums; no new RH estimate is proved",
                                "All exact coefficient laws survive arbitrary free-prime-monoid relabeling"],
            "proof": "coupling_proof.txt sections 5 through 8",
            "data": ["coupling-results/coupling_search.json", "coupling-results/coupling_verification.json",
                     "coupling-results/coupling_analytic_probe.json", "coupling-results/coupling_analytic_verification.json"],
            "counts_as_separate_new_operator": False,
        }, {
            "id": "paired_size_roots_and_zero_free_resonance_factor",
            "parent_candidates": ["floor_size_root_limit_transfer", "ceiling_size_root_limit_transfer"],
            "definition": "For g=f^beta, B=1/2*(g Kfloor g+g Kceil g-g*g+R_b(g*g)), where R_b keeps indices b^k",
            "laws": ["B_(b,beta)(f)=f^beta * R_b(f^beta) for all normalized inputs",
                     "For u, B(s)=zeta(s)^beta*R_(b,beta)(s) initially Re(s)>1",
                     "Every integer base b>=2 and real beta in [0,1]: correction holomorphic on Re(s)>0 and Re(R)>=1/(1+b^-Re(s))>1/2",
                     "RH iff every pole-cancelled dyadic paired root continues single-valuedly and holomorphically to Re(s)>1/2",
                     "Any fixed irrational beta in (0,1) gives the same RH-equivalent criterion; the implemented scalar grammar uses rational beta",
                     "R_b is an ordinary algebra homomorphism on all inputs iff b is prime"],
            "verification": {"kernel_programs_scored": size["kernel_grammar"]["programs_scored"],
                             "finite_training_fits": size["kernel_grammar"]["training_fits"],
                             "finite_held_out_survivors": size["kernel_grammar"]["held_out_survivors"],
                             "finite_fingerprint_classes_not_operator_count": size["kernel_grammar"]["distinct_finite_basis_fingerprints"],
                             "independent_exact_checks_passed": size_check["all_passed"],
                             "fresh_actual_zeta_points_two_formulas_each": len(size_analytic["actual_zeta_ball_checks"]),
                             "independent_ordinary_Fourier_and_ratio_series_verifier_passed": size_analytic_check["all_passed"],
                             "actual_simple_zeta_zero_and_paired_root_controls_passed": size_analytic["actual_critical_line_zero_control"]["all_passed"]},
            "individual_floor_square_formula": "F_beta^2-2*F_beta*J_beta+J_2beta, with J expressed by Fejer sums of vertically shifted zeta roots and an essential b-power resonance correction",
            "quantitative_spectral_domain": "Explicit infinite error bounds at Re(s)>2; Fourier identity at Re(s)>1",
            "scope": "Full half-plane root bridge is for the paired composition. The individual finite-q/U holomorphy gate is rejected by the separate size-resonance proof; no new RH estimate",
            "proof": "size_carry_proof.txt",
            "data": ["size-results/size_carry_search.json", "size-results/size_carry_verification.json",
                     "size-results/size_analytic_probe.json", "size-results/size_analytic_verification.json"],
            "counts_as_separate_new_operator": False,
        }, {
            "id": "size_lift_simplex_resonances_and_limit_growth_obstruction",
            "parent_candidates": ["floor_size_root_limit_transfer", "ceiling_size_root_limit_transfer"],
            "laws": ["For every finite q>=1, epsilon^alpha*L_q(u^alpha)(1+epsilon) tends to 1/q!",
                     "For every b>=2, alpha>0, q>=2 and nonzero integer m, epsilon^alpha*L_q(u^alpha)(1+epsilon+2*pi*i*m/log(b)) tends to a nonzero simplex Fourier coefficient",
                     "Floor coefficient is -sum_(r=1)^(q-1) w^r/(q-r)!, w=1/(2*pi*i*m); ceiling is its conjugate",
                     "U(u)(1+epsilon) grows faster than all log powers but slower than all positive powers of 1/epsilon",
                     "No finite real power of s-1 makes either U holomorphic at s=1"],
            "verification": {"volume_programs_scored": size_resonance["volume_grammar"]["models_scored"],
                             "training_fits": len(size_resonance["volume_grammar"]["training_fits"]),
                             "surviving_aliases_for_one_factorial_law": len(size_resonance["volume_grammar"]["survivors"]),
                             "actual_zeta_artificial_singularity_controls": len(size_resonance["artificial_singularity_checks"]),
                             "actual_zeta_angular_branch_controls": len(size_resonance["actual_zeta_log_angle_controls"]),
                             "independent_exact_and_Arb_gates": len(size_resonance_check["checks"]),
                             "independent_verifier_passed": size_resonance_check["all_passed"]},
            "gate_result": "Individual unmodified size lifts are excluded from the proposed RH-half-plane holomorphy criterion, independently of RH",
            "limits": ["This does not invalidate their formal arithmetic laws or the paired root identity",
                       "No isolated meromorphic pole or isolated essential singularity is asserted without local continuation",
                       "Fixed-order weak angular limits do not prove a Bessel asymptotic for actual U"],
            "proof": "size_resonance_proof.txt",
            "data": ["size-results/size_resonance_probe.json", "size-results/size_resonance_verification.json"],
            "counts_as_separate_new_operator": False,
        }, {
            "id": "joint_size_kernel_correlations_and_natural_boundary",
            "definition": "K_(b,c)=K_floor,b AND K_floor,c; V=EXP_Kjoint LOG_D; L_q is the q-fold joint product of the ordinary qth root",
            "laws": ["Pointwise intersection preserves associative unital divisor kernels; formal LOG/EXP transfers have the inverse and group law",
                     "All zeta-input finite lifts and their coefficient limit have coefficients in [0,1] and converge locally uniformly on Re(s)>1",
                     "For multiplicatively independent b,c and alpha>0, epsilon^alpha*L_q(1+epsilon+i*(m*tau_b+n*tau_c)) tends to A_q(m)*A_q(n)",
                     "For every finite q>=2 that coefficient is nonzero at every integer mode; their frequencies are dense, so Re(s)=1 is a natural boundary",
                     "For c=b^k the real-pole coefficient is binomial(k+q-1,q)/(k^q*q!), rather than the independent coefficient 1/(q!)^2",
                     "For (b,c)=(2,4), the common-power projection is R_4; a delta-only replacement changes the n=4 coefficient from 3/4 to 5/16"],
            "verification": {"Boolean_programs_scored": joint["boolean_grammar"]["models_scored"],
                             "Boolean_training_fits": joint["boolean_grammar"]["training_fits"],
                             "finite_held_out_survivors_not_new_operator_count": joint["boolean_grammar"]["held_out_survivors"],
                             "correlated_volume_programs_scored": joint["correlated_angle_volume_grammar"]["models_scored"],
                             "fresh_surviving_correlated_volume_laws": len(joint["correlated_angle_volume_grammar"]["survivors"]),
                             "large_integer_bivariate_cycle_profiles": joint_check["large_integer_profiles_checked"],
                             "fresh_actual_zeta_comparison_cases": len(joint_analytic["actual_zeta_ball_checks"]),
                             "actual_root_torus_moment_cases": len(joint_analytic["actual_root_torus_moment_controls"]["independent_records"]),
                             "actual_dependent_zero_frequency_controls": len(joint_analytic["actual_root_torus_moment_controls"]["dependent_records"]),
                             "independent_arithmetic_and_analytic_checks_passed": joint_check["all_passed"] and joint_analytic_check["all_passed"]},
            "scope": "The natural-boundary theorem is for two multiplicatively independent bases and finite q>=2; no extension to dependent bases, infinite root order, or many reciprocal logarithms is asserted",
            "gate_result": "The selected finite joint-size lifts are rejected as unmodified RH-strip diagnostics, independently of RH",
            "proof": "joint_size_proof.txt",
            "data": ["joint-results/joint_size_search.json", "joint-results/joint_size_verification.json",
                     "joint-results/joint_size_analytic.json", "joint-results/joint_size_analytic_verification.json"],
            "historical_status": "Intersection and abstract LOG/EXP transfers are known closure constructions. Originality of the precise boundary application is unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "signed_orientation_cancellation_and_projection_reduction",
            "definition": "W=(sum_four_joint_squares-P+R_b(P)+R_c(P)-cross+R_c(first)+R_b(second)-R_bc(P))/6, g=f^beta, P=g*g",
            "laws": ["A nonzero rational constant combination of the four fixed-orientation root lifts cancels every nonconstant Abelian mode iff q=2 and all weights are equal",
                     "For independent bases, every nonzero rational constant orientation combination at q>=3 has a natural boundary on Re(s)=1",
                     "The four-square bilinear identity has ten learned bundled coefficients (1,1,1,-1,-1,1,1,-1,-1,1), universally valid on arbitrary arithmetic inputs",
                     "W=g*(R_b(g)+R_c(g)+R_bc(g))/3; its zeta correction is holomorphic and nonzero on Re(s)>0 for every beta in [0,1]",
                     "RH iff all pole-cancelled dyadic W roots continue single-valuedly and holomorphically to Re(s)>1/2",
                     "Averaging kernels and averaging q-fold lifts differ: bases 2,3, q=3, n=8 give 3/4 versus 20/27",
                     "Prime-base average kernels are classical nonzero weighted transports; composite examples fail associativity"],
            "verification": {"signed_frequency_programs_scored": cancellation["frequency_grammar"]["models_scored"],
                             "single_mode_training_fits": cancellation["frequency_grammar"]["training_fits"],
                             "fresh_survivors": len(cancellation["frequency_grammar"]["survivors"]),
                             "exact_bilinear_training_equations": cancellation["bilinear_projection_identity"]["exact_training_equations"],
                             "independent_arithmetic_gates": len(cancellation_check["checks"]),
                             "independent_analytic_gates": len(cancellation_analytic_check["checks"]),
                             "fresh_zeta_points_two_representations_each": len(cancellation_analytic["actual_zeta_ball_checks"]),
                             "fresh_actual_critical_line_zero": cancellation_analytic["fresh_actual_critical_line_zero_control"]["disk_centre"],
                             "fresh_actual_zero_root_correction_cases": len(cancellation_analytic["fresh_actual_critical_line_zero_control"]["correction_records"]),
                             "independent_checks_passed": cancellation_check["all_passed"] and cancellation_analytic_check["all_passed"]},
            "scope": "The higher-order exclusion is for constant rational combinations of four fixed-orientation finite lifts with independent bases; averaging products, dependent bases, nonconstant weights and infinite limits need separate analysis",
            "proof": "cancellation_proof.txt",
            "data": ["cancellation-results/cancellation_search.json", "cancellation-results/cancellation_verification.json",
                     "cancellation-results/cancellation_analytic.json", "cancellation-results/cancellation_analytic_verification.json"],
            "historical_status": "The survivor reduces exactly to known paired-root/projection compositions. Originality of the precise signed-domain classification is unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "prime_binary_partition_recurrence_and_domain",
            "parent_candidate": "prime_binary_partition_regularizer",
            "definition": "F_beta(n)=1/k! times the sum over partitions of the bits of n-1 into blocks whose value plus one is a prime power; block p^r contributes beta/r, k=popcount(n-1)",
            "laws": ["For even n, F_beta(n)=sum_(r=1)^v2(n) beta/r*(k-r)!/k!*F_beta(n-2^r+1)",
                     "For every complex beta, the zeta-input series converges absolutely and locally uniformly on Re(s)>0, jointly entire in beta",
                     "For real beta in [0,1], factorial-normalized carry-free q-fold lifts of ordinary zeta^(beta/q) converge locally uniformly to F_beta on Re(s)>0",
                     "Actual prime labels matter: F_1(7)=1 and F_1(11)=3/4, although both are prime and have the same bit count of n-1",
                     "Ordinary additive EXP_A LOG_D has no convergent Dirichlet half-plane for a positive parameter",
                     "Reverse EXP_D LOG_A has series exp(sum_(k>=1)(zeta(s+k)-1)), zero-free off nonpositive-integer essential singularities"],
            "verification": {"normalization_programs_scored": mixed_index["normalization_grammar"]["models_scored"],
                             "recurrence_programs_scored": mixed_index["parity_recurrence_grammar"]["models_scored"],
                             "recurrence_training_fits": mixed_index["parity_recurrence_grammar"]["training_fit_count"],
                             "fresh_recurrence_survivors": len(mixed_index["parity_recurrence_grammar"]["survivors"]),
                             "independent_exact_gates": len(mixed_index_check["checks"]),
                             "independent_analytic_gates": len(mixed_index_analytic_check["checks"]),
                             "fresh_actual_zeta_input_comparison_cases": len(mixed_index_analytic["actual_zeta_ball_checks"]),
                             "native_log_zeta_decode_cutoffs": [64, 128],
                             "existing_actual_zero_disks_with_new_operator_controls": len(mixed_index_analytic["existing_actual_zero_new_operator_controls"]["records"]),
                             "independent_checks_passed": mixed_index_check["all_passed"] and mixed_index_analytic_check["all_passed"]},
            "native_zeta_scope": "N has a certified native-input coefficient-origin bridge, not a closed scalar formula in zeta(s). The reverse calibration has two independent direct scalar zeta representations.",
            "RH_scope": "B roots are distinct from D roots. Unconditional holomorphy of N across actual simple zeta zeros cannot supply an RH test by itself; no point value of N at those zeros or zero-free theorem for N is claimed.",
            "proof": "mixed_index_proof.txt",
            "data": ["mixed-index-results/mixed_index_search.json", "mixed-index-results/mixed_index_verification.json",
                     "mixed-index-results/mixed_index_analytic.json", "mixed-index-results/mixed_index_analytic_verification.json"],
            "historical_status": "Subset convolution, Bell partitions, diagonal transport and formal LOG/EXP are classical. Originality of this particular arithmetic application and recurrence is unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "quadratic_difference_cancellation_and_zero_preserving_continuation",
            "parent_candidate": "quadratic_index_difference_root_transfer",
            "definition": "A_m=sum_a (-1)^(m-a)*binom(m,a)*E_(n(n+a)); P_(m,k,beta)=EXP_D(beta*(I+A_m^k)*LOG_D)",
            "laws": ["Exact ordinary D unit-group automorphism at beta=1, with coefficient-local inverse",
                     "Ordinary fractional D roots commute with this transform on all normalized inputs",
                     "For m=2,k=2,beta=1, zeta-input coefficients at 20 and 45 are -1 and 1, rejecting prime-relabel invariance and multiplicativity",
                     "Iterated kernel degree d=2^k, universal vanishing below r=m*(2^k-1), with exact generic leading recurrence c_(k+1)=(-1)^m*(2^k*s+r_k)_m*c_k",
                     "Grouped Delta_(m,k) is holomorphic on Re(s)>-m+(m+1)/2^k",
                     "H_beta=zeta^beta*exp(beta*Delta); the correction is zero-free throughout that half-plane",
                     "If m>ell and -ell lies inside the proved domain, Delta(-ell)=0 and C_beta(-ell)=1",
                     "For m=6,k=1 the transformed integer-power zeta keeps the exact derivative at the trivial zero -2"],
            "verification": {"weight_programs_scored": difference["finite_difference_calibration"]["models_scored"],
                             "order_programs_scored": difference["cancellation_order_grammar"]["models_scored"],
                             "leading_programs_scored": difference["leading_recurrence_grammar"]["models_scored"],
                             "exact_kernel_profiles": len(difference["exact_kernel_profiles"]),
                             "independent_exact_gates": len(difference_check["checks"]),
                             "independent_analytic_gates": len(difference_analytic_check["checks"]),
                             "fresh_actual_zeta_comparison_cases": len(difference_analytic["actual_zeta_ball_checks"]),
                             "negative_grouped_domain_controls": len(difference_analytic["negative_grouped_domain_controls"]["records"]),
                             "critical_zero_disks_with_new_root_controls": len(difference_analytic["existing_actual_zero_new_operator_controls"]["records"]),
                             "additional_actual_trivial_zero": difference_analytic["actual_trivial_zero_control"]["disk_centre"],
                             "independent_checks_passed": difference_check["all_passed"] and difference_analytic_check["all_passed"]},
            "scope": "The cancellation/domain hierarchy is universal for integer m,k>=1. Ordinary negative-half-plane coefficient-series convergence is explicitly rejected. The root criterion supplies no new estimate establishing RH.",
            "proof": "difference_proof.txt",
            "data": ["difference-results/difference_search.json", "difference-results/difference_verification.json",
                     "difference-results/difference_analytic.json", "difference-results/difference_analytic_verification.json"],
            "historical_status": "Finite differences and formal LOG/EXP are classical. The precise iterated quadratic-index application and domain hierarchy have unresolved originality.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "nonlinear_root_anomaly_prime_sum_trees_and_odd_quotient",
            "parent_candidate": "nonlinear_prime_sum_log_coupling",
            "definition": "P_r=EXP_D(g+K_r(g,g)), g=LOG_D f, Phi_r(x,y)=xy(x+y)^r",
            "laws": ["Exact nonlinear coefficient-triangular inverse; K is commutative bilinear but generally nonassociative for positive r",
                     "Input/output root quotient EXP_D(beta*(beta-1)*K_r(g,g))",
                     "Inverse logarithm expands over ordered binary trees with classical Catalan total masses and distinct actual-integer labels",
                     "For every r>=1, restriction to odd indices satisfies O(P_r(f))=O(f)",
                     "On zeta input at r=3, coefficients 256 and 6561 are 2 and 1, rejecting prime-relabel invariance",
                     "On zeta input, P_3(u)(750)=3 but P_3(u)(2)*P_3(u)(375)=1, rejecting multiplicativity at coprime indices",
                     "Gamma_r has absolutely/local-uniformly convergent ordinary Dirichlet series on Re(s)>2/(r+2)",
                     "Input zeta roots have correction exp(beta^2*Gamma), output roots exp(beta*Gamma); both are zero-free on the correction domain",
                     "At beta=1 zeta zeros and multiplicities are preserved, with ordinary fractional-root monodromy retained"],
            "verification": {"homogeneity_programs_scored": pair["universal_root_constraint_grammar"]["models_scored"],
                             "root_amplitude_programs_scored": pair["input_root_amplitude_grammar"]["models_scored"],
                             "inverse_mass_programs_scored": pair["inverse_mass_recurrence_grammar"]["models_scored"],
                             "independent_exact_gates": len(pair_check["checks"]),
                             "independent_analytic_gates": len(pair_analytic_check["checks"]),
                             "fresh_actual_zeta_comparison_cases": len(pair_analytic["actual_zeta_ball_checks"]),
                             "existing_critical_zero_disks": len(pair_analytic["existing_actual_zero_new_operator_controls"]["records"]),
                             "ordinary_root_correction_controls": 12,
                             "independent_checks_passed": pair_check["all_passed"] and pair_analytic_check["all_passed"]},
            "scope": "The universal input-root restriction is a regularity-scoped theorem, not a ban on all nonlinear maps. The prime-sum certificate is a sufficient half-plane, not a maximal-domain classification. No new RH estimate is supplied.",
            "proof": "pair_proof.txt",
            "data": ["pair-results/pair_search.json", "pair-results/pair_verification.json",
                     "pair-results/pair_analytic.json", "pair-results/pair_analytic_verification.json"],
            "historical_status": "Catalan trees, beta Mellin inversion, Tornheim denominators and formal LOG/EXP are classical. Originality of the precise weighted nonlinear application remains unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "prime_sum_decode_restored_zero_obstruction_and_sharp_norm_loss",
            "parent_candidate": "prime_sum_sector_decoder",
            "encoded_parent_candidate": "nonlinear_prime_sum_log_coupling",
            "definition": "D_r h(p^e*q^f)=h(p^e*q^f*(p^e+q^f)^r), p!=q and r divides neither exponent; zero off this sector",
            "laws": ["Universal uniqueness of prime-power fibres with exactly two nonzero exponent residues modulo r",
                     "D_r E_r and E_r D_r are idempotent sector projections; both operators are linear partial coordinate permutations",
                     "For prime-power-supported augmentation inputs, D_r K_r(a,b) equals their r-filtered Dirichlet product minus the same-prime diagonal",
                     "On the zeta-derived correction, decoded coefficients are 2/(e*f) on the admissible two-prime sector",
                     "T_r=(LOG zeta(s)-LOG zeta(r*s)/r)^2-Q_r, initially Re(s)>1; Q_r holomorphic on Re(s)>1/2",
                     "Local extension Q_r=LOG zeta(2s)+B_r with B_r holomorphic on Re(s)>1/3",
                     "Decoded ordinary series has exact absolute abscissa 1, although encoded Gamma_3 converges on Re(s)>2/5",
                     "At a simple zeta zero, decoded monodromy jump is 4*pi*i*G_r-4*pi^2; encoded Gamma_3 is holomorphic across the tested disks",
                     "For sigma>0, D_r:A_sigma->A_tau bounded iff tau>=(r+1)*sigma; exact norm 6^(sigma-tau)*5^(r*sigma)",
                     "Pure power regularization shifts T_r to T_r(s+lambda); using source sigma>2/(r+2) and target 1/2 forces lambda>(3*r+2)/(2*(r+2))"],
            "verification": {"decoder_programs_scored": decode["decoder_grammar"]["models_scored"],
                             "training_fits": decode["decoder_grammar"]["training_fits"],
                             "fresh_survivors": len(decode["decoder_grammar"]["survivors"]),
                             "independent_exact_gates": len(decode_check["checks"]),
                             "independent_analytic_gates": len(decode_analytic_check["checks"]),
                             "exact_zeta_queries": len(decode["zeta_decoded_profile"]["queries"]),
                             "decoded_exact_cutoff": decode["zeta_decoded_profile"]["decoded_cutoff"],
                             "fresh_actual_zeta_comparison_cases": len(decode_analytic["actual_zeta_ball_checks"]),
                             "existing_zero_disks_with_restored_log_obstruction": len(decode_analytic["restored_actual_zero_obstruction_controls"]["records"]),
                             "native_repeated_factor_entry_regression_passed": decode["native_factor_entry_regression"]["wrong_last_entry_dictionary_rejected"],
                             "independent_checks_passed": decode_check["all_passed"] and decode_analytic_check["all_passed"]},
            "scope": "Uniqueness is proved only on the stated prime-power sector. The norm tradeoff concerns this decoder and pure power weights. Raw-zeta action is a known mask; no new RH estimate or general operator impossibility theorem is asserted.",
            "proof": "decode_proof.txt",
            "data": ["decode-results/pair_fibre_probe.json", "decode-results/decode_search.json",
                     "decode-results/decode_verification.json", "decode-results/decode_analytic.json",
                     "decode-results/decode_analytic_verification.json"],
            "historical_status": "Prime valuations, power-free decomposition, coordinate projections, Mobius inversion and zeta-log branching are classical. Originality of this arithmetic decoder application and sharp norm tradeoff remains unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "full_prime_pair_two_products_endpoint_and_Hilbert_domain",
            "parent_candidate": "prime_sum_sector_decoder",
            "encoded_parent_candidate": "nonlinear_prime_sum_log_coupling",
            "definition": "For prime-pair Phi_r(p,q)=pq(p+q)^r, B_r queries by pq and A_r aggregates queries by p+q; r>=2",
            "laws": ["Every prime-pair image has a unique fibre among ALL prime-power input pairs, including diagonal pairs",
                     "B_r K_r(a,b)=a*_D b and A_r K_r(a,b)=a*_+ b for unrelated prime-supported augmentation inputs",
                     "Zeta-derived outputs are classical ordered prime-product coefficients and ordered Goldbach counts; raw-zeta actions reduce to known masks/counts",
                     "The additive decoder has a nonzero kernel and no two-sided inverse",
                     "Prime-only encoded series has exact absolute abscissa 2/(r+2) and converges absolutely at its endpoint",
                     "Product output P(s)^2 has exact absolute abscissa 1; additive output has exact abscissa 2 and absolute convergence at 2",
                     "A_r:A_sigma->A_tau bounded iff tau>=(r+2)*sigma, exact norm 2^((2r+2)*sigma-2*tau)",
                     "B_r:A_sigma->A_tau bounded iff tau>=(r+1)*sigma, exact norm 4^((r+1)*sigma-tau)",
                     "Additive Hilbert norm squared is the supremum of weighted prime-pair row sums; bounded iff tau>=(r+2)*sigma+1/2 for sigma>=0",
                     "Product decoding restores prime-zeta-square logarithmic monodromy at both actual-zero disks; additive zero values or monodromy are not inferred"],
            "verification": {"programs_scored": prime_pair["prime_pair_decoder_grammar"]["models_scored"],
                             "training_fits": prime_pair["prime_pair_decoder_grammar"]["training_fits"],
                             "fresh_survivors": len(prime_pair["prime_pair_decoder_grammar"]["survivors"]),
                             "independent_exact_gates": len(prime_pair_check["checks"]),
                             "independent_analytic_gates": len(prime_pair_analytic_check["checks"]),
                             "complete_prime_power_fibre_queries": prime_pair_check["exact_zeta_audit"]["complete_prime_power_fibres_checked"],
                             "diagonal_queries": prime_pair_check["exact_zeta_audit"]["diagonal_queries"],
                             "source_sum_and_product_cutoffs": [2048, 8192],
                             "independent_sum_and_product_cutoffs": [3072, 12288],
                             "fresh_native_zeta_comparison_groups": len(prime_pair_analytic["actual_zeta_ball_checks"]),
                             "existing_zero_disks_with_product_branch_obstruction": len(prime_pair_analytic["full_prime_product_zero_obstruction_controls"]["records"]),
                             "independent_checks_passed": prime_pair_check["all_passed"] and prime_pair_analytic_check["all_passed"]},
            "scope": "Known convolution calibration and compound decoder consequence, not a new primitive. This stage's endpoint proof is PRIME-ONLY; visible_proof.txt section 7 supplies a later full-prime-power extension. Hilbert necessity uses averaged prime density, not the Goldbach conjecture. No additive critical-strip theorem is supplied.",
            "proof": "prime_pair_proof.txt",
            "data": ["prime-pair-results/prime_pair_search.json", "prime-pair-results/prime_pair_verification.json",
                     "prime-pair-results/prime_pair_analytic.json", "prime-pair-results/prime_pair_analytic_verification.json"],
            "historical_status": "Prime convolution/counts, Mobius inversion, PNT, beta Mellin inversion and row-norm algebra are classical. The exact encoded application and sharp norm hierarchy remain unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "residue_visible_same_prime_cancellation_and_full_endpoint_limit",
            "parent_candidate": "residue_visible_prime_power_product_decoder",
            "encoded_parent_candidate": "nonlinear_prime_sum_log_coupling",
            "definition": "Aggregate Phi_r(p^e,q^f) coordinates by their product when distinct-base exponents are individually nonzero modulo r, or the same-base exponent sum is nonzero modulo r; r>=3",
            "laws": ["Every accepted image has a unique complete unordered prime-power fibre; single-visible same-prime images satisfy U^(r+1)>N using the full visible factor U",
                     "Generic prime-power coupling decodes to the filtered ordinary Dirichlet product, restoring same-prime rows",
                     "Zeta coefficients first differ from the unfiltered logarithm square at 2^r by -2H_(r-1)/r",
                     "Local correction coefficients vanish below r and are universally bounded by one",
                     "U_r=(LOG zeta(s)-LOG zeta(rs)/r)^2+R_r, R_r holomorphic on Re(s)>1/r",
                     "On a chosen zero-free logarithm branch, U_r tends locally uniformly and exponentially to (LOG zeta)^2",
                     "For multiplicity m, the zero-loop anomaly from (LOG zeta)^2 is -4*pi*i*m*LOG zeta(rs)/r with a height-independent Euler bound",
                     "Absolute and positive-sigma Hilbert decoder maps are bounded iff tau>=(r+1)*sigma; the absolute norm and Hilbert norm for r*sigma>=1 are exactly 4^((r+1)*sigma-tau)",
                     "Same-prime aggregation has a nonzero kernel and is unbounded on unweighted l2; low-weight norm-one claims are rejected",
                     "The FULL prime-power encoded source converges absolutely at its exact abscissa 2/(r+2) and its endpoint norm is uniformly bounded for r>=3",
                     "Endpoint Hilbert decoding has exact norm one but target 2(r+1)/(r+2)>=8/5; no critical-line estimate follows"],
            "verification": {"classifier_programs": visible["single_visible_classifier_grammar"]["models_scored"],
                             "classifier_training_fits": visible["single_visible_classifier_grammar"]["training_fits"],
                             "reconstruction_programs": visible["same_prime_reconstruction_grammar"]["models_scored"],
                             "reconstruction_training_fits": visible["same_prime_reconstruction_grammar"]["training_fits"],
                             "cancellation_order_programs": visible["local_cancellation_grammar"]["order_models"],
                             "harmonic_leading_programs": visible["local_cancellation_grammar"]["leading_models"],
                             "independent_exact_gates": len(visible_check["checks"]),
                             "independent_analytic_gates": len(visible_analytic_check["checks"]),
                             "complete_prime_power_fibre_queries": visible_check["exact_zeta_audit"]["complete_prime_power_fibre_queries"],
                             "same_prime_queries": visible_check["exact_zeta_audit"]["same_prime_queries"],
                             "exact_parameter_profiles": [row["r"] for row in visible["zeta_profiles"]],
                             "source_and_independent_decoded_cutoffs": [8192, 12288],
                             "fresh_full_native_zeta_groups": len(visible_analytic["actual_zeta_ball_checks"]),
                             "fresh_subcritical_correction_only_controls": len(visible_analytic["deep_correction_ball_checks"]["records"]),
                             "actual_zero_parameter_controls_on_two_reused_disks": len(visible_analytic["restored_actual_zero_obstruction_controls"]["records"]),
                             "independent_checks_passed": visible_check["all_passed"] and visible_analytic_check["all_passed"]},
            "scope": "New detector family and verified compound consequences, not established historically-new mathematics. Deep-strip convergence concerns the additive remainder, not the full ordinary decoded series. Parameter limits require a chosen zero-free LOG branch. The full source endpoint sharpens prior sufficient domains without proving global PP injectivity or an RH estimate.",
            "proof": "visible_proof.txt",
            "data": ["visible-results/visible_search.json", "visible-results/visible_verification.json",
                     "visible-results/visible_analytic.json", "visible-results/visible_analytic_verification.json"],
            "historical_status": "Stirling/harmonic coefficients, root-of-unity filters, PNT, valuation reconstruction and zero monodromy are classical. The exact arithmetic application and combined bounds remain of unresolved originality.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "gap_correlation_endpoint_classification_and_one_sided_root_bridge",
            "parent_candidate": "nonlinear_prime_sum_log_coupling",
            "compound_transform": "gap_prime_pair_log_coupling",
            "definition": "Replace the sum index by ab|a-b|^r with a!=b, then apply EXP_D(h+K^-_r(h,h)) to h=LOG_D(f)",
            "laws": ["Exact coefficient-triangular inverse, odd-index quotient law, and quadratic input-root anomaly",
                     "Inverse leaf mass equals convolution mass minus actual equal-index overlaps; the simplified binary-tree law fails held-out collision seeds",
                     "Gamma^-_r=2*sum_(d>=1)d^(-rs)*sum_n g(n)g(n+d)/(n(n+d))^s, a known bilinear prime-pair correlation with g=Lambda/log",
                     "Exact absolute abscissa max(2/(r+2),1/2), independent of zero positions",
                     "Endpoint converges for r=1 and all r>=3, but diverges for r=2, unconditionally",
                     "For r>=3 the correction is holomorphic on Re(s)>1/2 and continuous on the closed half-plane",
                     "Input/output roots equal zeta^beta times exp(beta^2*Gamma) or exp(beta*Gamma); the full positive-beta ordinary series has absolute abscissa 1",
                     "At critical-line multiplicity m the one-sided root exponent is m*beta with a nonzero correction limit",
                     "The zero-diagonal Toeplitz kernel is indefinite and the critical-line l2 source norm diverges; endpoint convergence uses additional prime sparsity"],
            "verification": {"dimensional_threshold_programs": gap_probe["scaling_threshold_grammar"]["models_scored"],
                             "inverse_mass_programs": gap["inverse_mass_grammar"]["models_scored"],
                             "encoded_indices_checked": gap_check["zeta_audit"]["encoded_indices_checked"],
                             "finite_prime_density_certificates": gap_check["finite_density_audit"]["finite_density_certificates_checked"],
                             "independent_exact_gates": len(gap_check["checks"]),
                             "independent_analytic_gates": len(gap_analytic_check["checks"]),
                             "fresh_full_native_zeta_groups": len(gap_analytic["actual_zeta_ball_checks"]),
                             "ordinary_root_scalar_groups": len(gap_analytic["transformed_ordinary_root_scalar_controls"]["records"]),
                             "one_sided_zero_groups_on_two_reused_disks": len(gap_analytic["one_sided_actual_zero_controls"]["records"]),
                             "independent_checks_passed": gap_check["all_passed"] and gap_analytic_check["all_passed"]},
            "scope": "Known-kernel composite, not a new primitive. The threshold grammar fits explicit dimensional predictions, not an independent infinite numerical target. FFT values are exploratory. Endpoint convergence is proved with unconditional density/sieve estimates. Root preservation and RH equivalence do not exclude off-line zeros.",
            "proof": "gap_proof.txt",
            "data": ["gap-results/gap_endpoint_probe.json", "gap-results/gap_search.json", "gap-results/gap_verification.json",
                     "gap-results/gap_analytic.json", "gap-results/gap_analytic_verification.json"],
            "historical_status": "Prime-pair correlation, Toeplitz/FFT algebra and formal LOG/EXP are known. Originality of the specific weighted composite and endpoint application is unresolved; no verified historical novelty.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "prime_gap_Laplacian_shear_group_and_paired_domain_cancellation",
            "parent_candidate": "nonlinear_prime_sum_log_coupling",
            "compound_transform": "prime_gap_Laplacian_log_shear",
            "definition": "For h=LOG_D f, add t*sum_(p<q prime)h(p)h(q)[delta_(p^2*(q-p)^r)+delta_(q^2*(q-p)^r)-2delta_(p*q*(q-p)^r)], then apply EXP_D",
            "laws": ["The prime projection annihilates every correction, giving S_t S_u=S_(t+u) and the closed inverse S_(-t)",
                     "The odd-input support gives a separate valid shear; prime-power, squarefree, Omega<=2 and even support fail complete sparse composition",
                     "For even r, square output coefficients are positive and nonsquare outputs negative on the zeta input; all complete prime fibres are reconstructed",
                     "Paired H_r=sum_(p<q)(q-p)^(-rs)*(p^-s-q^-s)^2 is holomorphic on Re(s)>2/(r+2), with paired endpoint convergence for r>=3",
                     "For even r>=4 the ordinary correction coefficients instead have sharp absolute edge 1/2 with endpoint convergence",
                     "The sharp same-weight bilinear absolute norm is ((3/2)^sigma+(2/3)^sigma+2)/2; the zeta-prime input norm still diverges for sigma<=1",
                     "Input/output ordinary root factors use beta^2/beta and are nonzero on whole critical-zero disks at r=4",
                     "The real graph energy is positive; its complex Hermitian version is different from the holomorphic correction"],
            "verification": {"completion_programs": laplacian["diagonal_completion_grammar"]["models_scored"],
                             "support_masks": len(laplacian["support_mask_grammar"]["records"]),
                             "encoded_indices_checked": laplacian_check["zeta_audit"]["encoded_indices_checked"],
                             "independent_exact_gates": len(laplacian_check["checks"]),
                             "independent_analytic_gates": len(laplacian_analytic_check["checks"]),
                             "fresh_full_native_zeta_groups": len(laplacian_analytic["actual_zeta_ball_checks"]),
                             "ordinary_root_scalar_groups": len(laplacian_analytic["ordinary_root_scalar_controls"]["records"]),
                             "whole_zero_disk_groups_on_two_reused_disks": len(laplacian_analytic["whole_actual_zero_correction_controls"]["records"]),
                             "independent_checks_passed": laplacian_check["all_passed"] and laplacian_analytic_check["all_passed"]},
            "scope": "Known-kernel compound consequence, not a new primitive. The initial even-mask prefix false positive is archived and replaced by complete sparse composition. Grouped continuation must not be called ordinary coefficient convergence. Graph positivity does not identify Riemann zeros as eigenvalues.",
            "proof": "laplacian_proof.txt",
            "data": ["laplacian-results/laplacian_search.json", "laplacian-results/laplacian_verification.json",
                     "laplacian-results/laplacian_analytic.json", "laplacian-results/laplacian_analytic_verification.json"],
            "historical_status": "Graph Laplacians, second differences, prime projection, elementary shears and formal LOG/EXP are known. The exact arithmetic and domain/norm application has unresolved historical originality.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "higher_prime_moment_shear_uniform_height_limit_and_root_branching",
            "parent_candidate": "nonlinear_prime_sum_log_coupling",
            "compound_transform": "higher_prime_moment_shear_uniform_height_limit",
            "definition": "For even m>=2 and h=LOG_D f, add t*sum_(p<q prime,q-p>=2)h(p)h(q)*sum_j(-1)^j*binomial(m,j)*delta_(p^(m-j)*q^j*(q-p)^(m+2)), then EXP_D",
            "laws": ["Moment-annihilating weights are uniquely the classical alternating binomial row; bounded searches and higher-order exact linear solves recover them",
                     "Prime projection is fixed, giving the exact shear group and inverse; the smallest image is 4*6^m with coefficient f(3)*f(5)",
                     "Complete prime valuation-residue fibres reconstruct all faces, with square-positive/nonsquare-negative sign separation",
                     "Ordinary correction series converges absolutely on Re(s)>1/m; paired continuation is holomorphic on Re(s)>1/(m+1)",
                     "For m>=4, |R_m(s)|<=C(sigma)*(6^-sigma+10^-sigma)^(m-4), uniformly over all heights, with native prime-parity and integer-only majorants",
                     "The height-uniform identity limit has sharp threshold sigma*=0.34043184416498..., defined by 6^-sigma+10^-sigma=1; resonant 3/5 phases prevent decay at or below it",
                     "At Re(s)>=1/2 the m=64 correction-factor relative error is below 2.770e-9",
                     "Without the gap>=2 mask, the 2/3 edge causes scalar divergence on the critical line despite coefficientwise convergence to the identity",
                     "Ordinary input/output roots use beta^2/beta, independently of moment order; whole certified zeta-zero disks retain multiplicity*beta and fractional monodromy"],
            "verification": {"bounded_weight_programs": sum(row["models_scored"] for row in moment["moment_annihilation_grammar"]["bounded_search"]),
                             "finite_gap_mask_programs": moment["gap_support_mask_grammar"]["models_scored"],
                             "index_scale_programs": moment["image_scale_fit"]["models_scored"],
                             "finite_prime_input_encoded_queries": moment_check["zeta_audit"]["finite_prime_input_encoded_queries"],
                             "complete_zeta_prefix_indices_checked": moment_check["zeta_audit"]["complete_prefix_indices_checked"],
                             "independent_exact_gates": len(moment_check["checks"]),
                             "independent_analytic_gates": len(moment_analytic_check["checks"]),
                             "correction_factored_native_zeta_auxiliary_groups": len(moment_analytic["correction_native_zeta_auxiliary_groups"]["records"]),
                             "new_full_coefficient_origin_comparison_groups": 0,
                             "ordinary_root_scalar_groups": len(moment_analytic["ordinary_root_auxiliary_controls"]["records"]),
                             "whole_zero_disk_order_groups_on_two_reused_disks": len(moment_analytic["whole_actual_zero_root_controls"]["records"]),
                             "independent_checks_passed": moment_check["all_passed"] and moment_analytic_check["all_passed"]},
            "scope": "Known-kernel compound consequence; ten candidate families retained. A uniform relative correction factor estimate is not a bound excluding off-line zeta zeros. This stage adds no full coefficient-origin groups, leaving the then-current count at 138. Generic roots scale quadratically rather than by the binomial order. No new zero is located.",
            "proof": "moment_proof.txt",
            "data": ["moment-results/moment_search.json", "moment-results/moment_verification.json",
                     "moment-results/moment_analytic.json", "moment-results/moment_analytic_verification.json"],
            "historical_status": "Binomial finite differences, graph p-energies and prime logarithmic shears are known. Priority of the exact arithmetic encoding and uniform-height application remains unresolved.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "global_radix_self_similarity_complete_branch_ladder_and_root_fidelity_rejection",
            "parent_candidate": "global_degree_log_exp_root_limit",
            "compound_transform": "global_radix_degree_carry_log_exp_transfer",
            "definition": "S_b(f)=EXP_(G_b)(LOG_D f), G_b(f,g)(n)=sum_(ij=n)f(i)g(j)*1[s_b(Omega(i))+s_b(Omega(j))=s_b(Omega(n))], integer b>=2",
            "laws": ["The literal radix-digit kernel is associative and unital, with a universal normalized-unit-group transfer and inverse",
                     "Typed root commutation holds, but ordinary output roots fail even at coefficient eight: input half-root transfer 1/6 versus ordinary output half-root -1/48 for b=3",
                     "The continued zeta transform is a degree b-1 polynomial in LOG zeta, with coefficient functions holomorphic on Re(s)>1/2",
                     "Its leading H_(b-1)=F_(b,beta/b)(b*s) has an ordinary absolutely convergent series on Re(s)>1/b",
                     "For b>=3, 0<beta<=1, |H_(b-1)|>=2-zeta(b*Re(s))^(beta/b)>0 for all Re(s)>=1/2 and all heights",
                     "The complete (b-1)-st branch difference equals (2*pi*i*m*beta)^(b-1)*H_(b-1) at a zeta zero of multiplicity m",
                     "A single pointwise branch jump can vanish exactly in a controlled model while the complete second difference is nonzero",
                     "Rouche certifies a simple continued F_(3,1) zero near 0.872689+14.720036i, while ordinary zeta and S_3(zeta^(1/2)) are nonzero on the whole disk",
                     "Polynomial pole correction gives an RH-equivalent continuation criterion; its continuation remains unproved"],
            "verification": {"radix_degree_models_scored": radix["log_polynomial_grammar"]["radix_degree_models_scored"],
                             "complete_encoded_zeta_indices_checked": radix_check["encoded_zeta_indices_checked"],
                             "independent_exact_gates": len(radix_check["checks"]),
                             "independent_analytic_gates": len(radix_analytic_check["checks"]),
                             "new_full_coefficient_origin_comparison_groups": len(radix_analytic["actual_zeta_ball_checks"]),
                             "leading_self_similarity_auxiliary_groups": len(radix_analytic["leading_self_similarity_controls"]["records"]),
                             "ordinary_root_auxiliary_groups": len(radix_analytic["ordinary_root_auxiliary_controls"]["records"]),
                             "certified_created_operator_zeros": 1,
                             "reused_ordinary_zeta_zero_disks": 2,
                             "new_ordinary_zeta_zeros_located": 0,
                             "independent_checks_passed": radix_check["all_passed"] and radix_analytic_check["all_passed"]},
            "scope": "Nineteenth known-kernel consequence within ten existing candidate families. Six new full native-zeta groups bring the cumulative count to 144. The spurious transformed zero is not an ordinary zeta zero; strip values use analytic continuation, not an absolutely convergent ordinary Dirichlet series. The complete ladder detects logarithmic branching rather than preserving a fractional-root multiplier. No off-line zero is excluded.",
            "proof": "radix_proof.txt",
            "data": ["radix-results/radix_search.json", "radix-results/radix_verification.json",
                     "radix-results/radix_analytic.json", "radix-results/radix_analytic_verification.json"],
            "historical_status": "Digit-carry potentials, formal LOG/EXP and truncated graded algebras are known frameworks. The specific global-degree application and complete ladder have unresolved historical originality. The regular convolution historically called ternary is a different kernel; its name supplies neither a match nor novelty proof.",
            "counts_as_separate_new_operator": False,
        }, {
            "id": "actual_prime_all_scale_extraction_floor_trace_and_sharp_Mobius_decoder_barrier",
            "parent_calibration": "classical_arithmetic_LOG_Mobius_and_factorial_ratios",
            "compound_transform": "Landau_floor_prime_trace_and_Mobius_scale_decoder",
            "definition": "P(f)=sum_k mu(k)*U_k(LOG_D f)/k; w_c(t)=sum_a c_a*floor(a*t), sum_a a*c_a=0; T_c(X)=sum_n Lambda(n)*w_c(X/n); M T_c(X)=sum_m mu(m)*T_c(X/m)",
            "laws": ["Perfect-power dilation inversion recovers the actual prime indicator from zeta for every integer, with a universal inverse on generic formal inputs",
                     "Complete rational breakpoint positivity proves floor-filter positivity at every real scale, whereas a quarter-grid alias has actual zeta trace -2*log(2)",
                     "The all-scale trace equals sum_a c_a*log(floor(a*X)!); prime-power removal and residue masks give actual-prime observables",
                     "All 52 height-two survivors in the bounded grammar decompose into two height-one survivors; no universal decomposition theorem is claimed",
                     "Exact Mobius scale decoding gives sum_a c_a*psi(a*X), but can turn a positive trace into a negative prime-power contrast",
                     "Every finite floor trace cancels zeta-zero poles in its Mellin symbol; the central decoded contrast restores them at every nontrivial zero",
                     "The generic decoder has exact norm zeta(sigma)/zeta(2*sigma) for sigma>1 and is unbounded for sigma<=1; this does not rule out new cancellation on specific prime-derived inputs"],
            "prime_information": {"observables": ["actual prime indicator and residue counts", "complete scale-window prime counts and internal gaps", "weighted prime and prime-power mass", "all-scale factorial prime traces and decoded contrast"],
                                  "universal_identity_scope": "All integer indices and all real X>=0, with separately stated scale and support domains",
                                  "finite_observation_scope": "20 complete dyadic windows through 2**20 and four width-4096 windows through 10**12+4096",
                                  "new_uniform_prime_distribution_estimate_proved": False,
                                  "new_information_beyond_known_reconstruction_or_bounds_verified": False},
            "verification": {"prime_extraction_programs": prime_scale["prime_extraction_grammar"]["models_scored"],
                             "floor_programs": prime_scale["floor_filter_grammar"]["models_scored"],
                             "coarse_floor_survivors": prime_scale["floor_filter_grammar"]["coarse_grid_survivors"],
                             "universally_positive_floor_filters": len(prime_scale["floor_filter_grammar"]["certified_positive_filters"]),
                             "exact_factorial_trace_groups": len(prime_scale["universal_scale_identity_controls"]["floor_trace_exact_groups"]),
                             "complete_prime_observation_windows": len(prime_scale["actual_prime_scale_observations"]["records"]),
                             "independent_exact_gates": len(prime_scale_check["checks"]),
                             "independent_analytic_gates": len(prime_scale_analytic_check["checks"]),
                             "new_full_coefficient_origin_comparison_groups": len(prime_scale_analytic["actual_zeta_ball_checks"]),
                             "floor_trace_Mellin_auxiliary_groups": len(prime_scale_analytic["floor_trace_Mellin_auxiliary_checks"]["records"]),
                             "reused_zeta_zero_disks": 2,
                             "independent_checks_passed": prime_scale_check["all_passed"] and prime_scale_analytic_check["all_passed"]},
            "scope": "Twentieth known-framework consequence/calibration, with ten families retained. Finite windows near 10^12 are not an all-scale theorem. Six new complete prime-weight/native-zeta groups bring the total to 150. No new prime-distribution estimate, ordinary zero or RH proof is established; prime-specific arithmetic estimates are now the search priority.",
            "proof": "prime_scale_proof.txt",
            "data": ["prime-scale-results/prime_scale_search.json", "prime-scale-results/prime_scale_verification.json",
                     "prime-scale-results/prime_scale_analytic.json", "prime-scale-results/prime_scale_analytic_verification.json"],
            "historical_status": "Mobius inversion, prime extraction, factorial-ratio step functions and logarithmic-derivative prime weights are established. This is recovered calibration and a sharper research gate, not a claimed historical novelty.",
            "counts_as_separate_new_operator": False,
        }],
        "publication_history_audit": "novelty_audit.txt",
        "artifact_path_conventions": "Paths with a directory and proof .txt files are relative to the project directory. Bare result JSON filenames are in root-results/.",
        "compact_candidate_catalogue": "operator_candidates.txt",
        "proof_level": "Written universal mathematical proofs, supported by exact implementation checks; not theorem-prover certified",
        "novelty_rules": [
            "A finite numerical match is a candidate, not a universal theorem.",
            "An exact definition is not itself an interesting law or historical novelty.",
            "A new grammar macro composed from known primitives is not automatically a new mathematical operator.",
            "A proved formal law needs a separately proved analytic bridge and domain before it is called a zeta identity.",
            "No-match literature searches leave novelty unresolved; they do not verify novelty.",
        ],
        "candidates": [
            {"id": "normalized_rational_root", "status": "verified_rediscovery",
             "definition": "P_(1/q)(f)=sum_k binom(1/q,k)*(f-delta_1)^{*k}, f(1)=1",
             "laws": ["coefficient-local termination", "uniqueness", "q-fold Dirichlet power equals f"],
             "zeta_bridge": "For f=u and Re(s)>1, coefficients generate the normalized analytic qth root of zeta",
             "proof": "root_proofs.txt sections 1 and 3", "data": "root_probe.json",
             "prior_art": ["fractional_divisor_functions", "roots_of_multiplicative_functions", "rearick_log_exp_and_prime_derivations"], "counts_as_new": False},
            {"id": "root_denominator_digital_degree", "status": "proved_classical_valuation_consequence",
             "definition": "D_(q,ell)(n)=v_ell(q)*Omega(n)+sum_{p^e||n}v_ell(e!), prime ell|q",
             "laws": ["equals denominator valuation of b_(1/q)(n)", "equivalent base-prime digit-sum formula"],
             "proof": "root_proofs.txt section 4", "data": "root_probe.json",
             "novelty": "Derived from binomial coefficients and Legendre valuation arithmetic; no independent novelty asserted",
             "counts_as_new": False},
            {"id": "carry_weighted_divisor_product", "status": "verified_known_framework",
             "definition": "(a *_ell,t b)(n)=sum_{ij=n}t^[G_ell(ij)-G_ell(i)-G_ell(j)]a(i)b(j), G_ell(n)=sum_p v_ell(v_p(n)!)",
             "laws": ["associativity", "commutativity", "delta_1 identity", "at nonzero t, isomorphic to ordinary Dirichlet algebra"],
             "proof": "root_proofs.txt section 5", "data": "root_probe.json",
             "prior_art": ["weighted_transport", "nonzero_kernel_classification", "generalized_divisibility"], "counts_as_new": False},
            {"id": "unitary_zeta_root_lift", "status": "proved_root_application_novelty_unresolved",
             "definition": "L_q(f)=q-fold UNITARY convolution of P_(1/q)(f); for f=u, L_q(u)(n)=q^omega(n)*b_(1/q)(n)",
             "laws": ["ordinary quotient by u has squarefull support", "H_q(s)=zeta(s)*R_q(s)", "R_q holomorphic and nonzero on Re(s)>1/2"],
             "proof": "mixed_root_proofs.txt sections 1 through 4", "data": "mixed_root_search.json",
             "verification": "Exact direct/local implementations agree and 18 independent Arb checks satisfy explicit tail bounds",
             "RH_relevance": "H_q shares zeta's zeros in Re(s)>1/2. The identity gives no zero-free bound for H_q.",
             "novelty": "Unitary convolution and fractional divisor coefficients are known; the specific compound family requires further prior-art review",
             "counts_as_new": False},
            {"id": "carry_filtered_zeta_root_lifts", "status": "proved_root_applications_novelty_unresolved",
             "definition": "q-fold *_ell,t convolution of b_(1/q), followed by ordinary quotient by u",
             "laws": ["squarefull correction", "correction Euler product holomorphic on Re(s)>1/2", "nonvanishing proved for all 96 tested instances and two uniform parameter families"],
             "proof": "mixed_root_proofs.txt sections 1, 2 and 5; carry_zero_proof.txt; schur_root_proof.txt",
             "data": ["root-results/mixed_root_search.json", "root-results/carry_zero_audit.json", "root-results/carry_certificate_verification.json", "root-results/schur_root_audit.json"],
             "verification": {"passing_disk_instances": certified_count,
                              "norm_bound_certificates": carry["certified_count"],
                              "schur_plus_tail_certificates": schur["newly_certified"],
                              "schur_negative_and_positive_controls": schur_controls["all_passed"],
                              "independent_recomputed_coefficient_checks": carry_verification["all_passed"],
                              "uniform_parameter_theorems": carry["uniform_parameter_theorems"]},
             "limitations": ["The 96-instance audit is not a theorem for arbitrary carry parameters", "Known transport/divisibility frameworks may subsume these applications"],
             "counts_as_new": False},
            {"id": "multiplicative_shift_root_lowering", "status": "verified_classical_rediscoveries",
             "definition": "At a prime p: (v_p(n)+1)*b_alpha(p*n)=(v_p(n)+alpha)*b_alpha(n)",
             "grammar": "affine/additive/quotient/remainder/gcd index maps with polynomial weights",
             "verification": {"models_scored": shift["models_checked"], "training_fits": len(shift["training_candidates"]),
                              "fresh_survivors": len(shift["surviving_candidates"]), "all_survivors_have_classical_proofs": True},
             "proof": "shift_operator_proofs.txt", "data": "shift-results/shift_search.json",
             "prior_art": ["rearick_log_exp_and_prime_derivations"], "counts_as_new": False},
            {"id": "primewise_log_exp_root_limit", "status": "mathematically_verified_nonlinear_candidate_novelty_unresolved",
             "definition": "T(f)=EXP_infinitary(LOG_Dirichlet(f)), f(1)=1",
             "laws": ["normalized-unit-group isomorphism with an explicit inverse", "nonlinear, and target algebra contains nilpotents",
                      "coefficientwise and analytic root-order limit", "local exponent coefficients are set-partition sums of reciprocal bit-block sums",
                      "every integer q>=2 and q=infinity root lift has a holomorphic nonzero zeta correction on Re(s)>1/2",
                      "parameterized transfer admits exact dyadic coefficient extraction and a zero-free correction for every real beta in [0,1]"],
             "verification": {"independent_partition_and_Bernstein_witnesses": transfer_check["all_passed"],
                              "actual_zeta_ball_checks": len(transfer_analytic["actual_zeta_ball_checks"]),
                              "all_ball_checks_and_perturbation_controls_passed": transfer_analytic["all_passed"],
                              "uniform_bound": transfer["uniform_certificate"][0]["total_bound"]},
             "proof": "root_transfer_proof.txt", "data": ["transfer-results/root_transfer_probe.json", "transfer-results/root_transfer_verification.json", "transfer-results/transfer_analytic_probe.json"],
             "RH_relevance": "The beta=1 transform shares zeta's zeros; the dyadic beta family yields an RH-equivalent root-continuation criterion, without proving global continuation",
             "prior_art": ["infinitary_classical", "arithmetic_cross_group_operators", "formal_log_exp", "polymer_arithmetic_exp"],
             "additional_consequence": "dyadic_extraction_and_real_root_parameter",
             "novelty": "Exact compound statement not matched to a reviewed publication; components and abstract unit-group method are known. Search absence is not historical verification.",
             "counts_as_new": False},
            {"id": "global_degree_log_exp_root_limit", "status": "mathematically_verified_cross_prime_candidate_novelty_unresolved",
             "definition": "S(f)=EXP_G(LOG_Dirichlet(f)), (a G b)(n)=sum_ij=n 1[Omega(i)&Omega(j)=0]*a(i)*b(j)",
             "laws": ["coefficient-local nonlinear normalized-unit-group transfer", "q-fold global product of ordinary qth roots tends coefficientwise to S",
                      "S(u)=T(u) times the bit-disjoint-prime-exponent mask", "multiplicativity fails: S(u)(2)=S(u)(3)=1 but S(u)(6)=0",
                      "F(s)=A(s)*log(zeta(s))+B(s), A and B holomorphic on Re(s)>1/2, A not identically zero",
                      "F+A*log(s-1) extends holomorphically and single-valuedly to Re(s)>1/2 iff RH"],
             "verification": {"independent_arithmetic_and_partition_mask_coefficients_through": global_["mask_search"]["validation_cutoff"],
                              "mask_programs_scored": global_["mask_search"]["programs_checked"],
                              "actual_zeta_ball_checks": len(global_analytic["actual_zeta_ball_checks"]),
                              "all_ball_checks_and_perturbation_controls_passed": global_analytic["all_passed"],
                              "controlled_off_line_zero_detected": global_analytic["zero_sensitivity_control"]["all_passed"]},
             "proof": "global_carry_proof.txt", "data": ["global-results/global_carry_probe.json", "global-results/global_analytic_probe.json"],
             "RH_relevance": "The derived holomorphy criterion reacts to an off-line zero, but proving global extension remains equivalent to proving RH",
             "novelty": "Cross-prime zero-kernel/root-limit application requires further prior-art review; general potential-weight and logarithm/exponential frameworks are known",
             "counts_as_new": False},
            {"id": "canonical_prime_degree_projection", "status": "mathematically_verified_linear_candidate_novelty_unresolved",
             "definition": "M(f)(n)=(Omega(n)!/product_p v_p(n)! mod 2)*f(n)",
             "domain": "All rational arithmetic functions; typed algebra map from infinitary A to global degree G",
             "laws": ["unique diagonal A-to-G algebra homomorphism preserving every prime-power impulse",
                      "linear, unital and idempotent, with a nontrivial kernel",
                      "M(u)=chi; F_chi(s)=product_{j>=0}(1+P(2^j*s)) initially Re(s)>1",
                      "F_chi=C(s)*log(zeta(s))+C(s)*(1-Q(s)), C,Q holomorphic on Re(s)>1/2",
                      "F_chi+C*log(s-1) extends holomorphically and single-valuedly to Re(s)>1/2 iff RH"],
             "verification": {"mask_programs_scored": projection["search"]["programs_checked"],
                              "training_fits": len(projection["search"]["training_fits"]),
                              "equivalent_syntax_survivors": len(projection["search"]["survivors"]),
                              "independent_integer_parity_basis_pairs": projection_check["basis_pairs_checked"],
                              "independent_exact_checks_passed": projection_check["all_passed"],
                              "fresh_actual_zeta_points": len(projection_analytic["actual_zeta_ball_checks"]),
                              "analytic_representations_per_point": 2,
                              "all_ball_comparisons_and_perturbations_passed": projection_analytic["all_passed"],
                              "independent_Cauchy_zero_and_branch_verifier_passed": projection_analytic_check["all_passed"],
                              "actual_simple_zeta_zero_obstruction_certified": projection_analytic["actual_critical_line_zero_control"]["all_passed"]},
             "proof": "projection_proof.txt", "data": ["projection-results/projection_search.json", "projection-results/projection_verification.json", "projection-results/projection_analytic_probe.json", "projection-results/projection_analytic_verification.json"],
             "RH_relevance": "An explicit logarithmic zero-sensitive continuation criterion; global continuation remains unproved",
             "limitations": ["Zero preservation is rigorously rejected: a created simple transformed zero is certified where zeta is zero-free", "The parity mask and inverse sequence use established ingredients", "The hierarchy and cubic commutator are consequences, not separately counted primitives"],
             "prior_art": ["ordered_prime_multinomial", "prime_indicator_inverse", "multinomial_dirichlet_study", "bounded_exponent_factorization"],
             "novelty": "Specific canonical typed characterization and compound consequences have not been matched to reviewed literature; historical novelty remains unresolved",
             "counts_as_new": False},
            *[{"id": name, "status": "mathematically_verified_integer_order_candidate_novelty_unresolved",
               "definition": "U(f)=EXP_K(LOG_Dirichlet(f)); K selects " + orientation + "-height additive divisor splits",
               "height": "h=floor(log_b(n))" if orientation == "floor" else "H=ceil(log_b(n))",
               "domain": "Normalized characteristic-zero arithmetic functions, every integer base b>=2",
               "laws": ["commutative associative unital product, compatible with associative carry-only product",
                        "normalized unit-group transfer with explicit inverse",
                        "coefficientwise q-root limit on generic inputs",
                        "all zeta-input finite q lifts and their limit have coefficients in [0,1]",
                        "zeta-input limits converge locally uniformly on Re(s)>1",
                        "actual prime-value relabeling changes the product"],
               "verification": {"independent_exact_checks_passed": size_check["all_passed"],
                                "large_integer_cycle_profiles": size_check["large_integer_cycle_profiles_checked"]},
               "individual_zeta_bridge": "Absolute convergence on Re(s)>1; finite-power holomorphy at s=1 and the unmodified RH-half-plane gate are rejected by size_resonance_proof.txt",
               "RH_relevance": "The separate paired size-root composition has a nonzero correction and a proved RH-equivalent root-continuation criterion",
               "limitations": ["Assigned size construction also extends to normed free multiplicative monoids",
                              "Generic weighted convolution and LOG/EXP transfer frameworks are classical",
                              "Paired-root continuation cannot be attributed to individual U",
                              "Finite-q lifts create nonzero size-harmonic singularities on Re(s)=1",
                              "U has superlogarithmic but subpower growth at s=1, ruling out every finite-power pole cancellation"],
               "additional_consequence": "paired_size_roots_and_zero_free_resonance_factor",
               "prior_art": ["davison_general_divisor_kernels", "davison_normed_semigroups", "weighted_transport", "formal_log_exp"],
               "proof": "size_carry_proof.txt", "data": "size-results/size_carry_search.json",
               "novelty": "Exact application not matched to reviewed publications; historical originality unresolved",
               "counts_as_new": False}
              for name, orientation in (("floor_size_root_limit_transfer", "floor"),
                                        ("ceiling_size_root_limit_transfer", "ceil"))],
            {"id": "prime_binary_partition_regularizer", "status": "mathematically_verified_mixed_index_candidate_novelty_unresolved",
             "definition": "N_beta(f)=M EXP_shifted_additive_no_carry(beta LOG_D(f)); M(n)=1/popcount(n-1)!",
             "domain": "Normalized characteristic-zero arithmetic functions as formal coefficients; for zeta input, absolute/local-uniform Dirichlet convergence on Re(s)>0 for every complex beta",
             "laws": ["exact inverse N_1^-1=EXP_D LOG_C M^-1",
                      "unit-group homomorphism from D to the factorial-transported subset product B",
                      "typed B root law N_alpha B N_beta=N_(alpha+beta)",
                      "prime-power bit-block partition coefficient formula and universal v2 recurrence",
                      "joint holomorphy on Re(s)>0 and entire dependence on beta",
                      "real beta in [0,1] finite-root lifts converge locally uniformly on Re(s)>0"],
             "verification": {"independent_exact_checks_passed": mixed_index_check["all_passed"],
                              "independent_analytic_checks_passed": mixed_index_analytic_check["all_passed"],
                              "native_zeta_input_comparison_cases": len(mixed_index_analytic["actual_zeta_ball_checks"]),
                              "new_operator_controls_on_existing_actual_zero_disks": 2},
             "RH_relevance": "The ordinary-root interpretation is rejected algebraically and by monodromy at actual zeta zeros. The strong unconditional convergence is useful for arithmetic study but is not an RH diagnostic.",
             "limitations": ["No zero-free theorem for N on the critical strip", "No converged numerical point value of N at the actual zeta zeros is claimed",
                             "The native-zeta N comparison recovers input coefficients rather than claiming a closed scalar transform of zeta(s)",
                             "Classical constituent operations do not establish historical originality of the application"],
             "prior_art": ["classical_subset_convolution", "classical_Bell_partition_EGF", "formal_log_exp"],
             "proof": "mixed_index_proof.txt", "data": "mixed-index-results/mixed_index_search.json",
             "novelty": "Exact prime-binary application not matched to reviewed publications; historical originality unresolved",
             "counts_as_new": False},
            {"id": "quadratic_index_difference_root_transfer", "status": "mathematically_verified_ordinary_root_sensitive_candidate_novelty_unresolved",
             "definition": "P_(m,k,beta)(f)=EXP_D(beta*(I+A_m^k)*LOG_D(f)), A_m the finite difference of augmentation pushforwards n->n(n+a)",
             "domain": "All normalized characteristic-zero arithmetic functions as formal coefficients. Zeta-input series initially Re(s)>1; grouped analytic correction on Re(s)>-m+(m+1)/2^k",
             "laws": ["ordinary D group/root laws and exact inverse", "learned universal cancellation/leading coefficient hierarchy",
                      "zero-free correction and ordinary zeta zero multiplicity preservation in the proved domain",
                      "negative-integer correction equals one when m exceeds the integer magnitude and the point lies in the domain"],
             "verification": {"independent_exact_checks_passed": difference_check["all_passed"],
                              "independent_analytic_checks_passed": difference_analytic_check["all_passed"],
                              "actual_zeta_comparison_cases": len(difference_analytic["actual_zeta_ball_checks"]),
                              "critical_zero_disks": 2, "additional_trivial_zero": "-2"},
             "RH_relevance": "Retains ordinary-zeta fractional-root monodromy at actual zeros. All pole-cancelled dyadic roots give an RH-equivalent criterion, with no new estimate proving its continuation.",
             "limitations": ["Negative-domain correction is a grouped continuation, not absolute convergence of its ordinary coefficient series",
                             "Root preservation and stronger correction domains alone do not establish RH",
                             "Historical originality of the compound application remains unresolved"],
             "prior_art": ["classical_finite_difference_moments", "rearick_log_exp_and_prime_derivations", "formal_log_exp"],
             "proof": "difference_proof.txt", "data": "difference-results/difference_search.json",
             "counts_as_new": False},
            {"id": "nonlinear_prime_sum_log_coupling", "status": "mathematically_verified_nonlinear_log_candidate_novelty_unresolved",
             "definition": "P_r(f)=EXP_D(LOG_D(f)+K_r(LOG_D(f),LOG_D(f))), K_r sends (x,y) to xy(x+y)^r",
             "domain": "All normalized characteristic-zero arithmetic functions as formal coefficients. Zeta-input series initially Re(s)>1; ordinary correction converges absolutely on Re(s)>2/(r+2), with r=3 selected",
             "laws": ["exact coefficient-triangular inverse", "quadratic logarithmic root anomaly", "ordered inverse-tree expansion",
                      "odd-index quotient fixed for r>=1", "actual-prime-label dependence on zeta input",
                      "zero-free correction with ordinary zeta multiplicities retained"],
             "verification": {"independent_exact_checks_passed": pair_check["all_passed"],
                              "independent_analytic_checks_passed": pair_analytic_check["all_passed"],
                              "actual_zeta_comparison_cases": len(pair_analytic["actual_zeta_ball_checks"]),
                              "existing_critical_zero_disks": 2, "root_correction_controls": 12},
             "RH_relevance": "Retains ordinary-zeta fractional-root monodromy despite failing universal input-root commutation. The zero-preserving correction and dyadic reformulation supply no new RH estimate.",
             "limitations": ["Not an ordinary unit-group homomorphism; input and output root families differ",
                             "The bilinear index rule is generally nonassociative",
                             "The proved correction half-plane is sufficient; continuation outside it is unclassified",
                             "Historical originality of the weighted nonlinear application remains unresolved"],
             "prior_art": ["classical_Catalan_inverse_trees", "classical_Mordell_Tornheim_kernel", "classical_beta_integral", "formal_log_exp"],
             "proof": "pair_proof.txt", "data": "pair-results/pair_search.json", "counts_as_new": False},
            {"id": "gap_prime_pair_log_coupling", "status": "verified_known_prime_pair_correlation_compound_transform",
             "definition": "P^-_r(f)=EXP_D(LOG_D(f)+K^-_r(LOG_D(f),LOG_D(f))), K^-_r sends distinct indices a,b to ab|a-b|^r",
             "domain": "All normalized formal inputs. Zeta correction has exact absolute abscissa max(2/(r+2),1/2), with endpoint convergence iff r=1 or r>=3. Positive-beta full ordinary transformed series has abscissa 1",
             "laws": ["triangular inverse, odd quotient, bilinear root anomaly and exact overlap-dependent inverse mass",
                      "unconditional sharp abscissa and endpoint classification",
                      "ordinary-zeta root exponents retained from the right at critical-line zeros",
                      "classical bilinear Toeplitz correlation with explicit infinite numerical tails"],
             "verification": {"independent_exact_checks_passed": gap_check["all_passed"],
                              "independent_analytic_checks_passed": gap_analytic_check["all_passed"],
                              "fresh_full_comparison_groups": len(gap_analytic["actual_zeta_ball_checks"]),
                              "ordinary_root_scalar_groups": len(gap_analytic["transformed_ordinary_root_scalar_controls"]["records"]),
                              "one_sided_zero_groups": len(gap_analytic["one_sided_actual_zero_controls"]["records"]),
                              "complete_encoded_indices_checked": gap_check["zeta_audit"]["encoded_indices_checked"]},
             "RH_relevance": "r=3 gives a finite nonzero exponential factor up to the critical line and retains ordinary root behavior. All pole-cancelled dyadic roots yield an RH-equivalent criterion, with no estimate proving the required continuation",
             "limitations": ["Known prime-pair correlation calibration, not a new primitive",
                             "Not universally root commuting or an ordinary group homomorphism",
                             "Global prime-power injectivity fails for r=1; inverse-mass extrapolation fails held-out collision seeds",
                             "Whole critical-zero disk holomorphy is unproved; numerical root controls approach from the right only",
                             "Zero-diagonal kernel is indefinite; l2 source norm diverges on the critical line",
                             "FFT prefixes and dimension-generated grammar targets are not infinite convergence certificates",
                             "Specific weighted application originality remains unresolved"],
             "prior_art": ["classical_prime_pair_correlation_and_uniform_sieve", "classical_arbitrary_interval_Brun_Titchmarsh", "classical_prime_number_theorem", "formal_log_exp"],
             "proof": "gap_proof.txt", "data": "gap-results/gap_search.json", "counts_as_new": False},
            {"id": "prime_gap_Laplacian_log_shear", "status": "verified_known_graph_Laplacian_prime_logarithmic_shear",
             "definition": "S_t(f)=EXP_D(h+t*J_r(pi_prime h,pi_prime h)), with three gap images of weights 1,-2,1",
             "domain": "All normalized formal inputs. At r=4 the paired correction continues holomorphically to Re(s)>1/3, but its ordinary coefficient absolute edge is 1/2. The positive-beta full transformed ordinary series has absolute edge 1",
             "laws": ["exact additive-parameter composition group and inverse S_(-t)",
                      "complete prime fibres and square/nonsquare coefficient sign separation for even r",
                      "sharp bilinear same-weight coefficient norm and distinct paired convergence domain",
                      "ordinary-zeta root exponents retained with whole-disk nonzero correction bounds"],
             "verification": {"independent_exact_checks_passed": laplacian_check["all_passed"],
                              "independent_analytic_checks_passed": laplacian_analytic_check["all_passed"],
                              "fresh_full_comparison_groups": len(laplacian_analytic["actual_zeta_ball_checks"]),
                              "ordinary_root_scalar_groups": len(laplacian_analytic["ordinary_root_scalar_controls"]["records"]),
                              "whole_zero_disk_groups": len(laplacian_analytic["whole_actual_zero_correction_controls"]["records"])},
             "RH_relevance": "Finite-difference cancellation permits a correction holomorphic across critical-line zeros. All pole-cancelled dyadic roots give an RH-equivalent continuation criterion without proving its global estimate",
             "limitations": ["Known Laplacian/shear framework; historical originality unresolved",
                             "Not an ordinary group homomorphism and not universally input-root commuting",
                             "Ordinary coefficient convergence differs from grouped analytic continuation",
                             "The positive Hermitian form is not the complex holomorphic correction",
                             "Prime source norm diverges in A_sigma for sigma<=1 and in l2 for sigma<=1/2",
                             "No Riemann-zero spectrum, determinant or new RH estimate established"],
             "prior_art": ["classical_weighted_graph_Laplacian", "classical_prime_pair_correlation_and_uniform_sieve", "classical_prime_number_theorem", "formal_log_exp"],
             "proof": "laplacian_proof.txt", "data": "laplacian-results/laplacian_search.json", "counts_as_new": False},
            {"id": "prime_sum_sector_decoder", "status": "mathematically_verified_linear_partial_decoder_novelty_unresolved",
             "definition": "D_r h(p^e*q^f)=h(p^e*q^f*(p^e+q^f)^r), p!=q, r not dividing e,f; zero otherwise",
             "domain": "All formal coefficient sequences on the sector; r>=2. On weighted absolute coefficient spaces, bounded A_sigma->A_tau iff tau>=(r+1)*sigma for sigma>0",
             "laws": ["linear partial coordinate permutation with sector encoder and two projection inverse laws",
                      "generic prime-power coupling decoded to filtered Dirichlet product minus diagonal",
                      "exact weighted norm 6^(sigma-tau)*5^(r*sigma) in the bounded range",
                      "zeta-derived decoded series has absolute abscissa 1 and a proved scalar native-zeta identity"],
             "verification": {"independent_exact_checks_passed": decode_check["all_passed"],
                              "independent_analytic_checks_passed": decode_analytic_check["all_passed"],
                              "actual_zeta_comparison_cases": len(decode_analytic["actual_zeta_ball_checks"]),
                              "existing_critical_zero_disks": 2,
                              "complete_integer_fibre_queries": len(decode["zeta_decoded_profile"]["queries"])},
             "RH_relevance": "Decoding restores a squared-log obstruction at ordinary zeta zeros from a correction holomorphic there. The sharp norm cost prevents carrying the encoded holomorphy through at the same Dirichlet weight; an RH-equivalent continuation criterion gives no new estimate.",
             "limitations": ["D_r(delta_1)=0; not a normalized-unit-group map",
                             "Action directly on zeta's coefficient sequence is only a known two-prime mask",
                             "Global prime-power injectivity is not proved or used; unrestricted integer fibres collide",
                             "Missing encoded prefix coordinates cannot be replaced by zero",
                             "Pure power regularization makes the critical-zero obstruction shift left as it makes the decoder bounded",
                             "Historical originality of the specific application remains unresolved"],
             "prior_art": ["classical_unique_prime_factorization", "classical_scaled_Mobius_inversion", "classical_prime_zeta_zero_singularities"],
             "proof": "decode_proof.txt", "data": "decode-results/decode_search.json", "counts_as_new": False},
            {"id": "residue_visible_prime_power_product_decoder", "status": "mathematically_verified_linear_aggregating_decoder_novelty_unresolved",
             "definition": "V_r h(m)=sum_{x<=y in PP,xy=m,admissible}h(xy(x+y)^r), r>=3; distinct-base exponents or same-base total exponent must be nonzero modulo r",
             "domain": "All formal coefficient sequences; weighted absolute and Hilbert maps bounded iff tau>=(r+1)*sigma for sigma>0. The full scalar series initially converges on Re(s)>1, with a branch-valued zeta continuation and a single-valued remainder on Re(s)>1/r",
             "laws": ["universal complete-fibre uniqueness on the accepted two-visible and oversized single-visible sectors",
                      "generic filtered Dirichlet convolution retaining eligible same-prime products",
                      "exact absolute norm and high-weight Hilbert norm 4^((r+1)*sigma-tau)",
                      "harmonic local cancellation of order r and exact first defect at 2^r",
                      "full encoded endpoint convergence and a uniform endpoint source norm"],
             "verification": {"independent_exact_checks_passed": visible_check["all_passed"],
                              "independent_analytic_checks_passed": visible_analytic_check["all_passed"],
                              "fresh_full_comparison_groups": len(visible_analytic["actual_zeta_ball_checks"]),
                              "fresh_subcritical_remainder_controls": len(visible_analytic["deep_correction_ball_checks"]["records"]),
                              "actual_zero_parameter_controls": len(visible_analytic["restored_actual_zero_obstruction_controls"]["records"]),
                              "complete_prime_power_fibre_queries": visible_check["exact_zeta_audit"]["complete_prime_power_fibre_queries"]},
             "RH_relevance": "Restoring same-prime interactions cancels the separate order-two diagonal obstruction and leaves a remainder holomorphic on Re(s)>1/r, while actual ordinary-zeta logarithmic zero obstructions survive. The parameter-limit and endpoint bounds quantify this bridge but do not prove the missing RH-half-plane continuation.",
             "limitations": ["Aggregates coordinates, has a nonzero kernel, and is unbounded on unweighted l2",
                             "The decoded ordinary series still has exact absolute abscissa 1",
                             "The remainder is additive; it is not asserted zero-free",
                             "Local parameter limits are on chosen zero-free logarithm branches",
                             "The norm-one endpoint output weights remain at least 8/5",
                             "Raw-zeta action reduces to known masks/partition counts",
                             "The global PP index map and historical originality remain unresolved"],
             "prior_art": ["classical_unique_prime_factorization", "classical_Stirling_log_square_harmonics", "classical_prime_number_theorem", "classical_scaled_Mobius_inversion"],
             "proof": "visible_proof.txt", "data": "visible-results/visible_search.json", "counts_as_new": False},
        ],
        "rejections": [
            {"id": "short_floor_denominator_rules", "reason": "Some rules fit all training exponents but fail at e=9,25,49", "data": "root_probe.json"},
            {"id": "gcd_overlap_weight_associativity", "reason": "Impulse input indices 2,2,4 give weights 8 versus 4 at n=16", "data": "root_probe.json"},
            {"id": "unqualified_binomial_root_analytic_bridge", "reason": "Local radius is 1/q; positive real local singularities invalidate an automatic Re(s)>1/2 bridge", "proof": "mixed_root_proofs.txt section 5"},
            {"id": "squarefull_support_without_multiplicativity", "reason": "The input u+delta_6 gives a non-squarefull correction at n=12", "data": "mixed_root_search.json"},
            {"id": "global_mask_short_omega_fit", "reason": "Two degree-count masks fit through n=64 but fail at n=72", "data": "global-results/global_carry_probe.json"},
            {"id": "global_transfer_multiplicativity", "reason": "Coprime inputs 2 and 3 both have coefficient 1, but the coefficient at 6 is zero", "data": "global-results/global_carry_probe.json"},
            {"id": "non_dyadic_exponent_extraction", "reason": "26 fitted index maps fail fresh exponent/parameter checks; disjoint-bit impulses give a universal counterexample for every non-dyadic multiplier", "data": "dyadic-results/dyadic_root_search.json"},
            {"id": "finite_root_order_implies_RH", "reason": "A double zero passes the local square-root test; a quadruple zero passes square and fourth roots. All dyadic orders are needed by the proved criterion", "data": "dyadic-results/dyadic_analytic_probe.json"},
            {"id": "parameter_halving_for_arbitrary_inputs", "reason": "For f=delta_1+delta_2, E_2(T_1(f))(2)=-1/2 but T_(1/2)(f)(2)=+1/2. The parameter-scaling law uses the special zeta input u", "data": "dyadic-results/dyadic_root_search.json"},
            {"id": "short_diagonal_intertwiner_fits", "reason": "Nine of twelve training fits fail at fresh prime-power normalizations or basis-product identities; the remaining three expressions define the same mask", "data": "projection-results/projection_search.json"},
            {"id": "unqualified_global_equals_mask_primewise", "reason": "S=M T fails on EXP_Dirichlet(delta_6). The universally correct identity is M T=S P_2", "proof": "projection_proof.txt section 4"},
            {"id": "finite_prime_bases_complete_multiplicativity", "reason": "Bases 2,3,5,7 preserve the mixed-prime logarithmic impulse at n=3072 because its multinomial is 11; base 11 removes it", "proof": "projection_proof.txt section 5"},
            {"id": "linear_projection_preserves_zeta_zero_set", "reason": "F_chi has a certified simple zero near 1.1533968760+14.0166117003*i in a disk where actual zeta is Arb-certified nonzero", "proof": "projection_proof.txt section 11", "data": "projection-results/projection_analytic_probe.json"},
            {"id": "factorial_commutator_arity_one_extension", "reason": "The k>=2 factorial formula predicts alpha^3/2 at k=1, whereas the universal cubic coefficient is alpha^3", "proof": "coupling_proof.txt section 3"},
            {"id": "suspension_module_offset_five", "reason": "Offsets (0,1) and (0,5) both fit exponents 0..3, but (0,5) fails the true module kernel at a=4,b=0", "data": "coupling-results/coupling_search.json"},
            {"id": "suspension_action_is_commutative_product", "reason": "B(x,1)=0 while B(1,x)=x. The associative law proved is a module law over A", "proof": "coupling_proof.txt section 2"},
            {"id": "shifted_coprimality_product", "reason": "gcd(a-1,b-1)=1 with unit override fails associativity at (2,2,4), weights 0 versus 1", "data": "size-results/size_carry_search.json"},
            {"id": "additive_residue_carry_used_in_multiplicative_indices", "reason": "Residue carry modulo 5 fails at (2,2,6), weights 0 versus 1", "proof": "size_carry_proof.txt section 4"},
            {"id": "floor_quotient_transfer_is_new_primitive", "reason": "Above n=2*m+2 this transfer equals ordinary LOG on every normalized input; its zeta series is log(zeta) plus a finite Dirichlet polynomial", "proof": "size_carry_proof.txt section 4"},
            {"id": "composite_base_resonance_projection_is_homomorphism", "reason": "Base 6 and inputs delta+delta_2, delta+delta_3 give delta+delta_6 versus delta; base 4 also fails", "proof": "size_carry_proof.txt section 5"},
            {"id": "unqualified_sawtooth_vertical_zeta_formula", "reason": "Omitting the b-power resonance correction gives a nonzero error at all six fresh actual-zeta points", "data": "size-results/size_analytic_probe.json"},
            {"id": "individual_size_root_lift_RH_half_plane_holomorphy", "reason": "Every q>=2 creates nonzero artificial singularities at 1+2*pi*i*m/log(b), m!=0, independently of RH", "proof": "size_resonance_proof.txt section 2"},
            {"id": "finite_power_pole_cancellation_regularizes_size_U", "reason": "U grows faster than every log power and slower than every positive pole power at s=1; no finite real power cancellation can give a holomorphic germ", "proof": "size_resonance_proof.txt section 5"},
            {"id": "zero_root_order_residue_implies_regular_limit", "reason": "The finite-q residue 1/q! and epsilon*U both tend to zero, but U still has a nonmeromorphic growth obstruction at 1; zero Abelian residue does not imply regularity", "proof": "size_resonance_proof.txt section 5"},
            {"id": "uniform_angle_model_is_actual_Bessel_asymptotic", "reason": "Fixed-k weak limits give the classical uniform model I_0(2*sqrt(L)); they do not justify substituting uniform probabilities for a growing number of actual arithmetic terms", "proof": "size_resonance_proof.txt section 6"},
            {"id": "complement_of_joint_associative_kernel_is_associative", "reason": "For bases 2,3 the complement fails at (2,3,6), with weights 0 versus 1", "data": "joint-results/joint_size_verification.json"},
            {"id": "dependent_size_angles_are_independent", "reason": "For bases b,b^2 the real-pole coefficient at q=2 is 3/8, not 1/4; nonconstant torus mode (1,-2) has identically zero frequency", "proof": "joint_size_proof.txt section 4"},
            {"id": "common_power_projection_is_always_unit_only", "reason": "For bases 2,4 it is R_4; replacing it by the unit-only projection changes the n=4 lift coefficient from 3/4 to 5/16", "proof": "joint_size_proof.txt section 5"},
            {"id": "unmodified_independent_joint_size_lifts_cross_the_critical_strip", "reason": "Every finite q>=2 has a proved natural boundary on Re(s)=1, created by the filter itself", "proof": "joint_size_proof.txt sections 2 and 3"},
            {"id": "single_mixed_frequency_fit_proves_cancellation", "reason": "Only one of 39 training fits survives fresh axis and unequal-mode tests in the 1904-program signed grammar", "data": "cancellation-results/cancellation_search.json"},
            {"id": "constant_rational_orientation_weights_regularize_q_ge_3", "reason": "Every nonzero rational constant combination has dense nonzero Abelian modes and a natural boundary on Re(s)=1 for independent bases", "proof": "cancellation_proof.txt section 3"},
            {"id": "averaging_associative_kernels_always_preserves_associativity", "reason": "The normalized four-orientation average for bases 4,8 fails at (2,2,3), 0 versus 1/16; bases 2,6 also fail", "data": "cancellation-results/cancellation_search.json"},
            {"id": "averaging_root_lifts_equals_lifting_the_average_kernel", "reason": "Bases 2,3 at q=3,n=8 give 20/27 versus 3/4, a difference of 1/108", "proof": "cancellation_proof.txt section 6"},
            {"id": "common_power_base_is_the_larger_original_base", "reason": "Bases 4,8 have common positive powers 64^k, so the intersection projection is R_64 rather than R_8", "proof": "cancellation_proof.txt section 5"},
            {"id": "Dirichlet_nilpotence_bound_applies_to_additive_LOG", "reason": "At n=16, LOG_A(delta_1+delta_2)=1/15 but using the D floor(log2 n) factor bound gives zero", "proof": "mixed_index_proof.txt section 1"},
            {"id": "formal_additive_divisor_transfer_automatically_has_zeta_domain", "reason": "EXP_A LOG_D of the zeta input has no convergent Dirichlet half-plane for any positive parameter", "proof": "mixed_index_proof.txt section 6"},
            {"id": "mixed_index_formal_inverse_preserves_zeta_zeros", "reason": "EXP_D LOG_A is certified nonzero on both existing actual simple-zeta-zero disks", "data": "mixed-index-results/mixed_index_analytic_verification.json"},
            {"id": "typed_subset_roots_are_ordinary_zeta_roots", "reason": "At n=6, N_(1/2)(u)=1/8 while the ordinary D half-root of N_1(u) is zero; N is also holomorphic across actual simple zeta zeros", "proof": "mixed_index_proof.txt sections 2 and 8"},
            {"id": "unconditional_subset_root_holomorphy_proves_RH", "reason": "The factorial regularizer has an unconditional Re(s)>0 convergence theorem; its own B root law carries no ordinary-zeta monodromy implication", "proof": "mixed_index_proof.txt sections 5 and 8"},
            {"id": "quadratic_grouped_negative_domain_is_ordinary_Dirichlet_convergence", "reason": "For primes p>m the log-correction coefficient at p^(2^k) is (-1)^(m*k); individual terms fail to tend to zero on Re(s)<=0", "proof": "difference_proof.txt section 4"},
            {"id": "quadratic_cancellation_order_is_exact_for_every_s", "reason": "At s=0 the entire kernel is zero; the exact-order claim must exclude the finite roots of its leading polynomial", "data": "difference-results/difference_verification.json"},
            {"id": "first_inverse_difference_correction_is_always_enough", "reason": "A sparse control through 10^8 needs a second nonzero resolvent power; the first wrong coefficient is at n=65536", "data": "difference-results/difference_search.json"},
            {"id": "native_vanished_coefficients_alone_certify_difference_kernel", "reason": "A tuple can be interpreted by FLINT as a scalar ball; explicit coefficient lists, normalization and the nonzero leading coefficient are now checked", "proof": "difference_proof.txt section 9"},
            {"id": "universal_input_root_commutation_is_required_for_zeta_zero_sensitivity", "reason": "The prime-sum map has an exact quadratic root anomaly but both zeta root families retain ordinary-zero monodromy with zero-free corrections on Re(s)>2/5", "proof": "pair_proof.txt sections 3,5,7"},
            {"id": "prime_sum_bilinear_rule_is_an_associative_algebra", "reason": "Impulse indices 2,2,3 give different iterated image integers for positive r", "data": "pair-results/pair_search.json"},
            {"id": "r_zero_log_square_has_zero_free_holomorphic_correction_across_zeta_zeros", "reason": "Its logarithm-square correction has nonconstant monodromy exp(4*pi*i*LOG zeta-4*pi^2) at a simple zero", "proof": "pair_proof.txt section 7"},
            {"id": "unrestricted_integer_prime_sum_index_injectivity", "reason": "Phi_3(3,45)=Phi_3(16,20)=14929920; the bounded integer probe has 44 collisions, with a universal additional collision family", "data": "decode-results/pair_fibre_probe.json"},
            {"id": "encoded_holomorphy_survives_same_weight_decoding", "reason": "The sharp decoder criterion requires tau>=(r+1)*sigma. Actual-zero controls restore nonzero log jumps while encoded Gamma_3 is holomorphic on each whole disk", "proof": "decode_proof.txt sections 6,7"},
            {"id": "truncated_encoded_query_may_be_zero_filled", "reason": "Decoded index 10 needs encoded index 3430, unavailable in a prefix through 2048; missing infinite-series data is not an exact sparse zero", "data": "decode-results/decode_search.json"},
            {"id": "native_factor_entries_are_always_unique_prime_pairs", "reason": "The beyond-word held-out integer 36899117956198039606 has repeated factor entries; exponents must be summed and exact product reconstruction checked", "data": "decode-results/decode_verification.json"},
            {"id": "power_regularized_decoder_preserves_critical_zero_location_and_is_bounded", "reason": "The later full endpoint source sigma=2/5 and target tau=1/2 permit lambda>=11/10, still moving critical-line log obstructions to real part<=-3/5. The original open-domain certificate gave strict inequalities", "proof": "visible_proof.txt section 7; original decode_proof.txt section 7"},
            {"id": "prime_pair_sum_decoder_has_two_sided_inverse", "reason": "delta_21000-delta_25000 is a nonzero kernel vector at r=3, since both prime-pair sums are ten", "data": "prime-pair-results/prime_pair_search.json"},
            {"id": "prime_pair_sum_decoder_inherits_unweighted_partial_isometry", "reason": "Its l2 norm is the supremum of square-root prime-pair row counts, which is unbounded by prime-density averaging", "proof": "prime_pair_proof.txt section 7"},
            {"id": "increasing_prime_pair_encoding_power_reaches_RH_halfplane_by_bounded_sum_decode", "reason": "The sharp prime-only source endpoint is 2/(r+2), but generic bounded additive decoding always requires target weight at least 2", "proof": "prime_pair_proof.txt sections 5,6"},
            {"id": "absolute_convergence_abscissa_always_implies_endpoint_divergence", "reason": "The prime-only encoded component and unweighted additive prime-pair series converge absolutely at their exact abscissae", "proof": "prime_pair_proof.txt sections 4,5"},
            {"id": "weighted_Goldbach_continuation_applies_to_unweighted_prime_decode", "reason": "The reviewed prior Goldbach function uses von Mangoldt weights on all prime powers; the current output is an unweighted prime-only series", "proof": "prime_pair_proof.txt section 9"},
            {"id": "same_prime_visible_aggregation_is_an_unweighted_partial_isometry", "reason": "A p^k row has floor(k/2) image coordinates; the unweighted l2 norm is infinite and delta_16000-delta_8192 is a nonzero kernel vector", "proof": "visible_proof.txt sections 3,6"},
            {"id": "positive_sigma_Hilbert_boundary_norm_always_equals_one", "reason": "Exact low-weight same-prime row controls exceed one when r*sigma<1; the norm formula is proved with the condition r*sigma>=1", "data": "visible-results/visible_verification.json"},
            {"id": "deep_visible_remainder_convergence_proves_whole_decoded_series_convergence", "reason": "R_r converges on Re(s)>1/r, but U_r has ordinary absolute abscissa 1 and retains quadratic-log monodromy at zeta zeros", "proof": "visible_proof.txt sections 4,5"},
            {"id": "uniform_encoded_endpoint_bound_reaches_the_critical_line", "reason": "The full endpoint source norms are uniformly finite, but bounded norm-one output weights are 2(r+1)/(r+2)>=8/5 and tend to 2", "proof": "visible_proof.txt section 7"},
            {"id": "gap_inverse_has_universal_asymmetric_binary_tree_mass", "reason": "The conditional two-seed law predicts 240 at four leaves for seeds 2,3,5 and r=1, but the exact overlap identity gives 232 due to collisions at index 30", "proof": "gap_proof.txt section 1"},
            {"id": "increasing_gap_power_pushes_absolute_correction_edge_below_half", "reason": "PNT and bin-count Cauchy lower bounds from near prime pairs force divergence below 1/2 for every fixed r", "proof": "gap_proof.txt section 3"},
            {"id": "finite_gap_r_two_prefix_plateau_proves_endpoint_convergence", "reason": "An unconditional layer-cake prime-density bound makes the critical r=2 endpoint diverge; finite double-precision prefixes cannot establish an infinite limit", "proof": "gap_proof.txt section 4"},
            {"id": "bilinear_gap_correlation_can_be_replaced_by_Hermitian_correlation", "reason": "Conjugating the input introduces a different cosine phase and fails all six actual-zeta comparison groups", "data": "gap-results/gap_analytic_verification.json"},
            {"id": "gap_kernel_is_positive_semidefinite_and_has_finite_critical_l2_source", "reason": "delta_2-delta_3 gives a negative quadratic form, and the prime source norm includes divergent sum_p 1/p at the critical line", "proof": "gap_proof.txt section 6"},
            {"id": "continuous_gap_endpoint_proves_whole_zero_disk_holomorphy", "reason": "The proved endpoint is continuity on the closed right half-plane; it supplies one-sided root asymptotics, not correction holomorphy across the line or an RH estimate", "proof": "gap_proof.txt sections 4,5"},
            {"id": "prefix_even_mask_composition_proves_universal_log_shear", "reason": "The even mask passes through 2048 but complete sparse composition fails at 59105344; prime and odd masks survive with universal output-support proofs", "data": "laplacian-results/failed_truncated_mask_probe.json"},
            {"id": "paired_Laplacian_third_halfplane_is_ordinary_coefficient_convergence", "reason": "At r=4 the grouped correction is holomorphic on Re(s)>1/3, whereas sign separation makes the ordinary coefficient absolute edge exactly 1/2", "proof": "laplacian_proof.txt section 3"},
            {"id": "positive_prime_graph_energy_is_the_holomorphic_complex_correction", "reason": "Hermitian conjugation changes the form and all six full native-zeta scalar groups reject that replacement", "data": "laplacian-results/laplacian_analytic_verification.json"},
            {"id": "coefficientwise_identity_operator_limit_implies_scalar_identity_near_zeta_zeros", "reason": "For unmasked even moments, the first image 2^m moves to infinity but at 1/2+i*pi/log(3/2) the 2/3 prime edge grows like (1/sqrt(2)+1/sqrt(3))^m; the remaining correction decays uniformly", "proof": "moment_proof.txt section 5", "data": "moment-results/moment_analytic_verification.json"},
            {"id": "moment_annihilation_order_is_ordinary_input_root_scaling_degree", "reason": "The encoded index has binomial degree m but the prime logarithmic input occurs bilinearly; input root amplitude is beta^2, not beta^m", "proof": "moment_proof.txt section 1"},
            {"id": "composite_radix_binomial_nondivisibility_is_digit_carry", "reason": "Modulo-four binomial nondivisibility fails associativity at degrees 1,1,2, with parenthesizations 1 and 0. The true radix-four digit kernel gives zero on both", "proof": "radix_proof.txt section 1", "data": "radix-results/radix_verification.json"},
            {"id": "global_radix_three_matches_regular_ternary_convolution", "reason": "The published regular ternary product kills delta_p times delta_p; the global radix-three product gives delta_(p^2). A terminology match is not a kernel match", "proof": "radix_proof.txt section 8", "source": "regular_ternary_is_different_kernel"},
            {"id": "global_radix_typed_roots_preserve_ordinary_output_roots", "reason": "Radix three gives input/output half-root coefficients 1/6 and -1/48 at eight. It also has a certified simple transformed zero where ordinary zeta and the transformed input half-root are nonzero", "proof": "radix_proof.txt sections 1 and 6", "data": "radix-results/radix_analytic_verification.json"},
            {"id": "single_pointwise_loop_jump_completely_detects_zeta_branching", "reason": "A controlled quadratic-LOG model has an exactly zero first scalar jump but a nonzero complete second branch difference; the full ladder detects the zero", "proof": "radix_proof.txt section 5", "data": "radix-results/radix_analytic_verification.json"},
            {"id": "radix_transformed_strip_zero_is_a_zeta_counterexample", "reason": "The whole certified disk near 0.872689+14.720036i has native zeta modulus greater than 0.4895. The located zero belongs to the continued operator, not zeta", "proof": "radix_proof.txt section 6", "data": "radix-results/radix_analytic.json"},
            {"id": "small_radix_residual_is_a_zero_certificate", "reason": "The initial coarse Rouche bound failed and remains archived. Only the positive-margin producer and independently changed nested disk certify a zero of the infinite operator", "proof": "radix_proof.txt sections 6 and 7", "data": "radix-results/failed_radix_outer_bound.json"},
            {"id": "coarse_floor_grid_positivity_is_all_scale_prime_trace_positivity", "reason": "The quarter-grid alias has w(1/7)=-2 and actual zeta trace -2*log 2 at X=2/7. Complete breakpoint certificates reject it", "proof": "prime_scale_proof.txt section 2", "data": "prime-scale-results/prime_scale_verification.json"},
            {"id": "positive_floor_prime_trace_has_positive_Mobius_decode", "reason": "At X=5 the trace is log 252>0 but the decoded contrast is psi(10)-2psi(5)=log(7/10)<0", "proof": "prime_scale_proof.txt section 3", "data": "prime-scale-results/prime_scale_analytic_verification.json"},
            {"id": "all_scale_floor_trace_holomorphy_is_an_RH_test", "reason": "Every finite floor trace cancels the zeta-zero poles of -zeta_prime/zeta in its Mellin symbol. The decoded central contrast restores them", "proof": "prime_scale_proof.txt section 4", "data": "prime-scale-results/prime_scale_analytic_verification.json"},
            {"id": "generic_Mobius_scale_decoder_is_bounded_at_critical_weight", "reason": "Exact saturating vectors and elementary squarefree-density blocks prove unboundedness for sigma<=1. A structured arithmetic improvement needs a new argument", "proof": "prime_scale_proof.txt section 5"},
            {"id": "complete_finite_prime_windows_prove_all_scale_distribution_bounds", "reason": "Every integer in 24 windows is independently checked, including near 10^12, but those observations do not cover all larger scales or prove a uniform estimate", "proof": "prime_scale_proof.txt section 3"},
        ],
        "sources": sources,
        "next_search_requirements": [
            "PRIORITY: find an operator with new arithmetic information about actual prime counts, weighted mass, gaps, correlations or residues across all scales. State the observable, parameters and proved range.",
            "Separate direct prime extraction or reconstruction from a new identity or uniform estimate; remove prime-power contamination and do not infer all-scale bounds from finite windows.",
            "Seek a new cancellation estimate for unsmoothed prime-window/residue observables or their decoded contrasts. Finite floor traces cancel zeta-zero poles, and their generic Mobius decoder norm cannot reach the critical weight.",
            "Separate mere changes of coordinates and known composites from candidate operators with new arithmetic consequences.",
            "Resolve publication history of the two mathematically verified nonlinear transfers and their specific zeta consequences, including dyadic extraction and the continuous real-parameter certificate.",
            "Audit the canonical linear A-to-G projection against multinomial parity, characteristic-two arithmetic inverses, and monomial-quotient frameworks before any novelty claim.",
            "Search genuinely new arithmetic consequences of cross-prime coupling with proved analytic domains and zero-sensitive controls.",
            "Investigate a usable global estimate for the transformed functions; a root/zero-preserving identity or RH equivalence alone does not resolve RH.",
            "Do not extrapolate the proved selected first-other-prime bridge to the full factorial/multi-prime commutator; prove the missing global bounds separately.",
            "Resolve publication history of the size-carry kernels and paired identity; integer-value dependence alone is insufficient for a new primitive.",
            "Preserve the negative regularity gate: individual size lifts require new singularity subtractions, since ordinary pole cancellation is now disproved.",
            "Preserve the joint natural-boundary gate: multiplicatively independent size intersections cannot be used unmodified to cross Re(s)=1; dependent bases and infinite root order require separate analysis.",
            "Preserve the signed-cancellation classification: equal q=2 weights reduce to known projection compositions; all nonzero rational constant combinations at q>=3 retain the independent-base barrier.",
            "Search beyond these constant orientation combinations for a genuinely new arithmetic consequence or global bound; a normalized corrected root alone is only another RH-equivalent reformulation.",
            "Expand addition/residue grammars with correct typed index laws and prove a stronger arithmetic consequence than a weighted transport or root-continuation reformulation.",
            "Keep the mixed-index positive calibration and its root-information rejection: a convergent typed root in a new product is not automatically an ordinary zeta root.",
            "Audit publication history of the prime-binary partition application and seek a proved ordinary-zeta zero-sensitive bound before attributing RH relevance to further mixed-index constructions.",
            "Audit the quadratic-difference operator's specific cancellation/domain hierarchy; finite differences and LOG/EXP alone are not originality evidence.",
            "Use the verified ordinary-root bridge and its critical/trivial-zero controls to search for a new quantitative estimate, while keeping grouped continuation distinct from coefficient-series convergence.",
            "Allow nonlinear logarithmic terms without requiring universal input-root commutation; prove their ordinary-zeta zero bridge independently and retain the exact root anomaly.",
            "Audit prime-sum weighted Tornheim applications and seek a new arithmetic identity or quantitative bound beyond another zero-free explicit factor; Catalan inverse masses are classical.",
            "Audit the specific prime-sum decoder and sharp norm tradeoff; retain its raw-zeta known-mask reduction and sector scope when judging novelty.",
            "Search for arithmetic decoders or controlled estimates that improve this sharp domain loss without disguising a classical power shift or assuming global prime-power injectivity.",
            "Keep the full prime-pair product/additive rediscovery controls, diagonal uniqueness proof, sharp endpoint distinctions and the additional Hilbert row-count loss.",
            "Seek a genuinely new arithmetic identity or zeta-specific quantitative estimate beyond classical Goldbach counts; do not transfer the product's zero obstruction or weighted prior-art continuation to the unweighted additive series.",
            "Preserve the residue-visible same-prime cancellation and complete-fibre proof; the deep-strip remainder identity must not be presented as full decoded Dirichlet convergence.",
            "Seek a zeta-specific estimate that improves the proved generic decoder loss or a stronger arithmetic law beyond the classical logarithm-square parameter limit. Retain the full endpoint refinement, low-weight Hilbert counterexamples and actual-zero controls.",
            "Retain the gap correlation's sharp 1/2 barrier and endpoint distinction. Seek an arithmetic estimate beyond the known-kernel root factorization; increasing its power cannot push its absolute abscissa left of 1/2.",
            "Preserve the bilinear/Hermitian distinction and failed positive-semidefinite kernel gate. Any spectral RH proposal needs a separate positivity and critical-source argument.",
            "Explore higher cancellation orders and support-preserving shears only with complete sparse compositions, ordinary-root bridges and separately proved paired/coefficient domains. Known graph energy or an explicit nonzero factor alone is not historical novelty or an RH estimate.",
            "Retain the radix ordinary-output-root fidelity rejection. Universal unit-group transfer laws and typed root commutation are insufficient to preserve ordinary zeta-root locations.",
            "Use complete branch differences through the polynomial LOG degree, actual-zero controls and certified zeta-zero-free artifact controls; one scalar return value after a loop is an incomplete zero-sensitivity test.",
            "Preserve literal radix digits for composite bases; Lucas/binomial nondivisibility is a prime-base calibration only.",
            "Investigate parameter limits only with uniform analytic estimates, not coefficientwise stabilization. Seek a new arithmetic law or a quantitative zeta estimate beyond another RH-equivalent LOG-polynomial continuation criterion.",
        ],
    }
    maximum_training = max(float(x["training_error"]) for x in matches.values())
    maximum_validation = max(float(x["validation_error"]) for x in matches.values())
    exact_laws = sum(len(record["laws"]) for record in root["exact_grammar"]["random_input_records"])
    bridge_count = (len(root["analytic_bridge"]) + len(mixed["unitary_analytic_checks"])
                    + len(transfer_analytic["actual_zeta_ball_checks"]) + len(global_analytic["actual_zeta_ball_checks"])
                    + len(dyadic_analytic["actual_zeta_ball_checks"])
                    + len(projection_analytic["actual_zeta_ball_checks"])
                    + len(coupling_analytic["actual_zeta_ball_checks"])
                    + len(size_analytic["actual_zeta_ball_checks"])
                    + len(joint_analytic["actual_zeta_ball_checks"])
                    + len(cancellation_analytic["actual_zeta_ball_checks"])
                    + len(mixed_index_analytic["actual_zeta_ball_checks"])
                    + len(difference_analytic["actual_zeta_ball_checks"])
                    + len(pair_analytic["actual_zeta_ball_checks"])
                    + len(decode_analytic["actual_zeta_ball_checks"])
                    + len(prime_pair_analytic["actual_zeta_ball_checks"])
                    + len(visible_analytic["actual_zeta_ball_checks"])
                    + len(gap_analytic["actual_zeta_ball_checks"])
                    + len(laplacian_analytic["actual_zeta_ball_checks"])
                    + len(radix_analytic["actual_zeta_ball_checks"])
                    + len(prime_scale_analytic["actual_zeta_ball_checks"]))
    registry["full_coefficient_origin_native_zeta_comparison_groups"] = bridge_count
    registry["verified_arithmetic_consequence_count"] = len(registry["verified_arithmetic_consequences"])
    assert bridge_count == 150 and registry["verified_arithmetic_consequence_count"] == 20
    (output_dir / "candidate_registry.json").write_text(json.dumps(registry, indent=2) + "\n")
    statuses = Counter(record["analytic_bridge_status"] for record in mixed["candidates"])
    statuses["proved_holomorphic_correction_Re_s_gt_half_nonvanishing_unresolved"] -= certified_count
    statuses["proved_nonzero_correction_Re_s_gt_half_by_certified_disk_bounds"] = certified_count
    statuses = {key:value for key,value in statuses.items() if value}
    report = f"""EXPANDED ZETA OPERATOR DETECTOR

Primary research target: independently proved signed arithmetic control of
ordinary zeta at every scale, working toward RH. Historical priority is an
annotation and does not gate mathematical acceptance. No RH-sufficient uniform
signed estimate has been proved; the research objective remains open.
Known imported logarithmic signed control has a separate dependency scope.
Actual-prime observables and their scale scope remain relevant evidence.
Exact count/residue extraction and floor-trace identities are calibrations.
Finite complete windows near 10^12 are not an all-scale theorem. Root laws,
prime-power removal, arithmetic information gain and scale scope are now
separate candidate gates.
The grammar also searches representations, anti-linear maps, defects and
unknown phase kernels. A new global-moment layer searches inequalities,
mixed-energy recurrences and positive functionals. Universal support and
scale-cost certificates, rather than an exponent fit, justify its bounds.
Unrelated recursive and arithmetic families provide calibration; no QRH
exponent or theta construction is a training target.
Seven nonlinear arithmetic families and three linear operators now
pass mathematical verification in their stated domains. The two integer-size
transfers have proved individual series only on Re(s)>1; their proposed
finite-power RH-half-plane holomorphy gate is now rigorously rejected.
Their paired-root
composition has the separate nonzero-correction bridge on Re(s)>1/2.
Historical originality is recorded separately from mathematical verification.
The detector also recovered classical operators.
Universal laws have written proofs; none is claimed theorem-prover certified.
The selected two-base floor intersections have a proved natural boundary
on Re(s)=1 for every finite q>=2 with independent bases. They remain valid
arithmetic products, but fail the proposed unmodified RH-strip domain gate.
The signed search identifies a unique equal-weight q=2 cancellation and
proves a corrected root bridge; it reduces to known projection compositions.
Every nonzero rational constant orientation combination at q>=3 still has
the independent-base natural boundary. The new root controls include a
freshly located and certified actual critical-line zero near 21.02204i.
The mixed additive/divisor grammar yields a factorial-normalized subset
transfer with a proved zeta-input domain Re(s)>0 and a learned, universally
proved v2 recurrence. Its own typed roots differ from ordinary Dirichlet
roots, so their unconditional regularity does not supply an RH test.
The quadratic-difference stage preserves ordinary D roots and proves
a zero-free correction on Re(s)>-m+(m+1)/2^k. Its grouped negative-domain
continuation retains actual-zeta branching, with an additional verified
trivial-zero control at -2. Historical originality remains unresolved.
The nonlinear prime-sum stage broadens the grammar beyond linear LOG
coordinates. Its input-root amplitude beta^2 differs from output amplitude
beta, yet both retain ordinary-zeta zero monodromy with a zero-free
correction on Re(s)>2/5. Its odd-index quotient is fixed. It supplies no
new RH estimate and does not establish historical originality.
The residue-visible product decoder restores eligible same-prime rows and
proves a remainder holomorphic on Re(s)>1/r. Its actual-zero obstruction
survives, and its parameter limit approaches the classical logarithm square
on a chosen zero-free branch. A full prime-power endpoint theorem now
improves the earlier sufficient encoded domains, while the exact decoder
norm still leaves a substantial loss before reaching the critical line.
The difference-index extension recovers a known prime-pair correlation.
Its sharp abscissa is max(2/(r+2),1/2), with an unconditional convergent
critical endpoint for r>=3 and a divergent one for r=2. At r=3 it retains
one-sided ordinary-zeta root behavior with a finite nonzero correction;
it provides neither whole critical-zero disk holomorphy nor an RH estimate.
The prime-only Laplacian completion cancels the near-diagonal difficulty
in a grouped sum and gives a correction holomorphic on Re(s)>1/3 at r=4.
It has a closed logarithmic shear inverse and whole-zero disk bounds;
ordinary correction coefficients still have absolute edge 1/2.

New grammar: coefficient-local rational powers/roots, formal LOG/EXP, typed
normalization, deeper integer expressions with quotient/remainder/digit sums,
prime exponents, factorial valuations, affine index shifts, different
arithmetic products, root-order limits, and cross-prime degree coupling.
Later stages learn exponent extraction, real parameter scaling, diagonal
maps between typed products, prime-base projection hierarchies, and
polynomial laws for interactions between operator words. The newest stage
adds labelled tensor variables, arity-dependent factorials, typed
module actions, integer floor/ceiling sizes, residues and addition, and
signed orientation combinations with learned power-projection identities.
It now adds explicitly reindexed additive and carry-free bit-set products,
factorial normalizations, and prime-power additive block partitions.
The latest expansion adds nonlinear LOG couplings, prime-sum index
grafting, ordered inverse trees and an explicit input/output-root anomaly.
The generic root construction uses no prime-factor coefficient formula.
Factorization/digital features are explicitly enabled in the later stage.

ACTUAL ZETA ROOT RECONSTRUCTION
Root orders recovered: {sum(x['accepted'] for x in matches.values())}/{len(matches)} (2 through 7).
Label-blind rational-power programs scored: {root['root_grammar']['programs_checked']}.
Training: 16 coefficients from sigma=28, 120 numerical zeta points, cutoff 40.
Validation: 32 coefficients from sigma=50, 192 fresh points, cutoff 64.
Maximum training coefficient error: {maximum_training:.6g}.
Maximum held-out coefficient error: {maximum_validation:.6g}.
These reconstruction errors are empirical estimates, not certified enclosures.
The exact root programs separately pass {exact_laws} implementation law checks
on unrelated rational inputs at four cutoffs and reject invalid normalization.

ROOT DENOMINATOR SEARCH
Two-feature rules scored: {sum(x['programs_checked'] for x in root['denominator_search'])}.
Training fits: {len(denominator_matches)}; surviving exponent-96 checks: {len(denominator_survivors)}.
False training fits rejected: {len(denominator_rejected)}.
The true alternatives are equivalent expressions, not {len(denominator_survivors)} different operators.
For prime ell|q, the interpreted universal law is
  v_ell(denominator(b_(1/q)(n)))
    =v_ell(q)*Omega(n)+sum_{{p^e||n}}v_ell(e!).
For q=2 this is 2*Omega(n)-sum_p binary_digit_sum(v_p(n)).
Denominator defects yield associative carry-weighted divisor products.
Their nonzero-parameter algebras are known transports of Dirichlet algebra;
the zero-parameter binary case is classical infinitary convolution.

MIXED ROOT APPLICATION SEARCH
Programs explored: {mixed['programs_checked']}.
Coefficient support checked through n={mixed['validation_cutoff']}.
Ordinary quotients have squarefull support: proved using the cancelled first
local coefficient, and checked exactly. Squarefull does not mean square.
Analytic classifications: {statuses}.

The unitary family H_q(n)=q^omega(n)*b_(1/q)(n) satisfies
  H_q(s)=zeta(s)*R_q(s),
  R_q(s)=product_p[q*(1-p^(-s))^(1-1/q)-(q-1)*(1-p^(-s))].
R_q is proved holomorphic and nonzero on Re(s)>1/2. H_q therefore shares
zeta's zeros there, so this transformation does not resolve RH. The operator
is a composition of known primitives; its specific application is under
literature review and is NOT counted as verified novel.

CERTIFIED NUMERICAL BRIDGES AND NEGATIVE CONTROLS
Arb ball checks with explicit proved series/product tails: {bridge_count}/{bridge_count} passed.
Those checks cover roots, unitary lifts, transfer families, the linear
projection, a selected commutator sector, and paired integer-size roots at
their stated sample points. Six mixed-index cases also cover native-log-zeta
coefficient recovery and the direct reverse shifted-zeta transfer. The N
comparison is a coefficient-origin bridge, not a claimed closed scalar
formula in zeta(s). The six ordinary-root quadratic-difference cases have
direct scalar zeta representations and an independently grouped prime-power
reference. Wider analytic domains are established by mathematical proof,
not by those sample points. Twenty-four nonlinear-candidate checks additionally
reject controlled coefficient perturbations at every sample point. Six fresh
linear-projection points each pass two analytic representations and reject
the same perturbation with both proved error bounds.
Carry-family exact associativity/commutativity/identity checks: 20/20 passed.
Exact norm bounds certify {carry['certified_count']}/96 carry-root instances.
Arb Schur reduction plus proved analytic tails certifies the remaining
{schur['newly_certified']}: all {certified_count}/96 corrections are nonzero on Re(s)>1/2.
The Schur implementation passes 7 controls, including an interior zero
hidden after its first passing reduction and an excessive analytic tail.
A separate verifier
recomputed all 96 coefficient/bound records using integer binomial valuations
and rising-factor root coefficients: all passed = {carry_verification['all_passed']}.

Two uniform theorems follow from the coefficient bounds, for EVERY integer q>=2:
  prime ell>=5 and 0<=t<=1: correction holomorphic and nonzero on Re(s)>1/2;
  prime ell>=7 and -1<=t<=1: the same conclusion.
These are proved for whole parameter families, not extrapolated from finite q.
Their specific publication history remains unresolved; the constituent
operators have prior art and are not counted as verified new operators.

AFFINE INDEX GRAMMAR
Index/weight models scored: {shift['models_checked']}.
Training fits: {len(shift['training_candidates'])}; fresh survivors: {len(shift['surviving_candidates'])}.
All survivors have universal proofs as classical root-lowering recurrences,
including disguised composite-valuation identities. Fresh parameters include
negative and non-reciprocal rationals. The numerical zeta-root residual is
at most 4.03e-17. These are variants of known laws, not new operators.

NONLINEAR ROOT-LIMIT CANDIDATE T
  T(f)=EXP_infinitary(LOG_Dirichlet(f)), f(1)=1.
It transfers normalized unit groups and has an explicit inverse. It is
nonlinear; its target contains nilpotents, so it is distinct from a linear
scalar-weight transport of the ordinary Dirichlet algebra.
For u(n)=1 its local coefficient h_e is the sum over partitions of the bits
of e of products of reciprocal block sums. An independent implementation
recomputed all coefficient polynomials and exact Bernstein witnesses.
One certificate covers EVERY integer q>=2 and the q->infinity limit:
  |R_q(x)-1| <= {transfer['uniform_certificate'][0]['total_decimal_diagnostic']:.10f} < 1, |x|<=0.71.
Thus all these root lifts share zeta's zeros on Re(s)>1/2. Their corrections
also converge locally uniformly there as q->infinity. Six independent Arb
checks at fresh actual zeta arguments pass explicit series/product tails.

DYADIC EXTRACTION AND A CONTINUOUS FRACTIONAL-ROOT PARAMETER
  T_beta(f)=EXP_infinitary(beta*LOG_Dirichlet(f)),
  E_m(f)(n)=f(n^m).
Index maps scored: {dyadic['search']['models_scored']}; training fits: {dyadic['search']['training_fits']}.
Fresh survivors: {[x['multiplier'] for x in dyadic['search']['survivors']]}.
The other 26 fitted maps fail at held-out exponents or parameters. The
independent rational bit-partition route reproduces every fit decision.
For all inputs, E_m preserves infinitary convolution iff m is a power of 2.
For the zeta coefficient function u, the universally proved law is
  T_beta(u)(n^(2^k))=T_(beta/2^k)(u)(n).
Extending parameter halving to all normalized inputs is explicitly rejected:
f=delta_1+delta_2 gives -1/2 versus +1/2 at the extracted index n=2.
Lookahead is explicit: integer cutoff N needs N^m input; the local search
uses exponents through 384. No unavailable coefficient is padded with zero.

One exact degree-48 certificate proves, for EVERY real beta in [0,1],
  |R_beta(x)-1| <= {dyadic['uniform_real_parameter_certificate']['total_decimal_diagnostic']:.12f} < 1, |x|<=0.71.
Here H_beta(s)=zeta(s)^beta*R_beta(s) initially Re(s)>1, and R_beta is
holomorphic and nonzero on Re(s)>1/2. This is a continuous parameter theorem,
distinct from the earlier alpha=1/q finite-root-lift certificate.
Twelve fresh actual-zeta Arb comparisons pass, with every coefficient
perturbation rejected. Generic arithmetic and independent partition routes
agree for beta=1/2,1/4,1/8 through n=512.

Let Phi_k=(s-1)^(1/2^k)*H_(1/2^k). The proved criterion is
  RH iff EVERY Phi_k has a single-valued holomorphic extension to Re(s)>1/2.
A zero of order m would require 2^k to divide m for every k, which is
impossible. The controlled zero models demonstrate the finite-order trap:
double zeros pass square roots; quadruple zeros pass square and fourth
roots; the next larger dyadic root detects their branch obstruction.
The actual test disk is Arb-certified zero-free; no claim about actual
off-line zeros elsewhere is made. Global continuation remains unproved.
An additional control rigorously isolates one ACTUAL simple zeta zero in a
disk of radius 1/10000 centered at 1/2+14.13472514173469379046*i. Arb Taylor
bounds and Rouche count one simple zero; reflection forces Re(rho)=1/2.
Cancelling the quadratic correction through zeta(2s)^(-beta^2/2) proves
that R_beta extends without zeros to that entire crossing disk, using a
separate Arb nonzero enclosure for zeta(2s). All four tested dyadic roots
have certified branch obstructions there, with diagnostic winding one.
This boundary-zero control is compatible with RH; its circle crosses the
critical line. No global zero count or off-line-zero inference is claimed.
Thirteen additional cases use genuine arithmetic inputs with series
zeta^m, m=1,2,4,8: generic transfer coefficients through n=128, the proved
parameter-composition law, and actual-zero winding all agree. The square
root of zeta^2 and the fourth root of zeta^4 have no branch jump there;
their next larger dyadic roots do. These controls correspond to the
specified arithmetic inputs, rather than only artificial zero models.
This law extends T's arithmetic consequences and is not counted as a
separate new operator by renaming a parameterized known composition.

CROSS-PRIME CANDIDATE S AND THE ROOT ZETA ISSUE
  (a G b)(n)=sum_ij=n 1[Omega(i)&Omega(j)=0]a(i)b(j),
  S(f)=EXP_G(LOG_Dirichlet(f)).
The global degree restriction couples different primes. For example,
S(u)(2)=S(u)(3)=1 but S(u)(6)=0; multiplicativity is explicitly rejected.
At finite root order q the coefficient at 6 is exactly 1/q.
The detector scored {global_['mask_search']['programs_checked']} digital-mask rules. Five fit n<=64;
three equivalent rules survive to n=4096. Two false rules fail at n=72.
The recovered universal law is
  S(u)(n)=T(u)(n)*1[sum_p s_2(v_p(n))=s_2(Omega(n))].
The generic arithmetic and independent bit-partition/mask routes agree
exactly through n=4096.

The proved analytic representation is
  F(s)=sum_n S(u)(n)n^(-s)=A(s)*log(zeta(s))+B(s), initially Re(s)>1,
where A,B are holomorphic on Re(s)>1/2 and A is not identically zero.
After cancelling the known pole in the logarithm,
  Phi(s)=F(s)+A(s)*log(s-1),
  RH <=> Phi extends holomorphically and single-valuedly to Re(s)>1/2.
Six actual-zeta Arb comparisons with independent graded/Dirichlet routes
and proved tails pass. A controlled extra off-line zero produces a certified
nonzero logarithmic monodromy; the actual local comparison disk is certified
zero-free by Arb. This is a test of the derived criterion, not an RH claim.
The criterion exposes the needed global property. Proving that property is
still equivalent to RH and has NOT been achieved.

CANONICAL LINEAR PROJECTION AND INTERACTIONS BETWEEN TRANSFORMS
  M(f)(n)=chi(n)*f(n),
  chi(n)=[Omega(n)!/product_p v_p(n)!] mod 2.
The detector learns from basis-product identities and prime-power
normalization, without target mask labels. Programs scored:
{projection['search']['programs_checked']}; training fits: {len(projection['search']['training_fits'])};
held-out survivors: {len(projection['search']['survivors'])} equivalent expressions for ONE operator.
An independent integer/binomial-parity implementation checks all
{projection_check['basis_pairs_checked']} basis pairs through n={projection_check['cutoff']}.
The universal theorem characterizes M uniquely among diagonal A-to-G
algebra homomorphisms preserving every prime-power impulse. It is unital,
linear and idempotent; it is neither an ordinary nor G endomorphism.

With P_b=EXP_Dirichlet M_b LOG_Dirichlet, all these normalized ordinary
unit-group projections are idempotent and commute. The exact typed law is
  M(T(f))=S(P_2(f)), for every normalized input.
Unqualified S=M T fails; it holds exactly when LOG_Dirichlet(f) is
supported on the kept mask. That includes multiplicative inputs and some
nonmultiplicative ones. All prime-base projections converge coefficientwise
to CLASSICAL multiplicative completion. No fixed finite set suffices:
bases 2,3,5,7 miss n=3072=2^10*3, whose multinomial is 11.

The operator-word grammar and a separate symbolic calculation recover
  (T S f-S T f)(p^2*q)=f(p)^2*f(q), p,q distinct primes.
The full commutator vanishes at all prime powers and squarefree indices.
Its full half-plane analytic bridge has not been established; it is not
promoted to a separately verified RH-domain operator.

For the raw zeta input, the proved product is
  F_chi=product_{{j>=0}}(1+P(2^j*s)), initially Re(s)>1.
Here P is the prime zeta function. With C=product_{{j>=1}}(1+P(2^j*s))
and Q=sum_{{k>=2}}P(k*s)/k, both holomorphic on Re(s)>1/2,
  F_chi=C*log(zeta)+C*(1-Q).
The pole-cancelled F_chi+C*log(s-1) has a single-valued holomorphic
extension to Re(s)>1/2 iff RH. This is a reformulation, not a proof.
Six fresh actual-zeta points each pass the independent binary-product and
affine-log representations with proved infinite tails. Both reject each
coefficient perturbation. The actual simple critical-line zero is also
detected: Arb/Rouche isolates it, and ten certified rectangles connect
the P(2s) logarithm to its normalized Euler branch. The full C product
continues without zeros on that crossing disk, certifying a nonzero
2*pi*i*C monodromy. This test is compatible with RH. A further search finds
a CREATED zero of F_chi near 1.1533968760+14.0166117003*i. Arb/Taylor/Rouche
with the infinite Mobius and product tails proves a simple zero in a
radius-1e-6 disk, while actual zeta is certified nonzero there. This rejects
zero preservation by M; it is not an RH counterexample. Historical novelty
remains unresolved. A separate checker imports no production helpers and
repeats the created-zero count with Cauchy bounds on a larger disk and a
different Mobius cutoff. It rejects a deliberately incorrect log branch
and independently recomputes every critical-zero branch corridor and C
tail: all passed={projection_analytic_check['all_passed']}.

DEEPER INTERACTION GRAMMAR AND A SELECTED ZERO-SENSITIVE SECTOR
Factorial programs scored: {coupling['factorial_grammar']['programs_scored']}.
Training fits: {len(coupling['factorial_grammar']['training_fits'])}; equivalent survivors:
{len(coupling['factorial_grammar']['survivors'])} expressions for ONE law. For distinct primes,
  (T S-S T)(u^{{*alpha}})(p^2*q_1*...*q_k)
    =(-1)^(k+1)*k!/2*alpha^(k+2), k>=2.
At k=1 the exact answer is alpha^3, so extending that factorial expression
to arity one is rejected. Seven parameters and labelled arities through
16 pass; the independent EGF evaluator checks
{coupling_check['tensor_coefficients_independently_compared']} tensor coefficients.
The universal proof is an exact rational identity in a square-zero label
algebra, rather than extrapolation from these numerical samples.

The module grammar searches 64 exponent-offset pairs. Two fit small
exponents, one survives the fresh range: B(t,k)_e=sum_(a+b=e)
1[a&(b+1)=0]*t_a*k_b. For F=F_0+y F_1 with y^2=0,
  T(F)=t+y(t A k), S(F)=t+y B(t,k),
where t=EXP_A(log F_0), k=F_1/F_0. B is a unital A-module action, not a
commutative product. The learned false offset (0,5) fails at (4,0).

For d_e=(T S u-S T u)(p^e*q), the independently checked local expansion
through degree {coupling_check['local_degree_independently_compared']} has a proved infinite
weighted-norm bound on radius 39/50. Define A=sum_p d(p^-s) and
B=sum_p p^-s*d(p^-s); both are holomorphic on Re(s)>1/2. The SELECTED
sector C_1=sum_(p!=q,e>=2)d_e*(p^e*q)^(-s) obeys C_1=A*P-B on Re(s)>1.
Thus RH iff C_1+A*log(s-1) continues single-valuedly and holomorphically
to Re(s)>1/2. Six fresh actual-zeta comparisons and all coefficient-12
perturbations pass their explicit infinite tails. A separate verifier uses
different degree/Dirichlet/Mobius cutoffs and bounds: all passed=
{coupling_analytic_check['all_passed']}.

At the certified actual simple zero near 1/2+14.134725i, a normalized
P(2s) branch corridor and the degree-256 infinite-tail certificate give
|A|>0.587775 on the entire crossing disk, so the logarithmic jump has
modulus >3.69310. The independent verifier recomputes the corridor using
eight rectangles and counts the actual zero with a larger-disk Cauchy
remainder. This detects an actual boundary zero and is compatible with RH.

The full commutator's half-plane bridge remains unestablished. These laws
survive free-prime relabeling, and this sector reduces to A*P-B; no new
estimate excluding off-line zeta zeros has been proved. A named sector or
composition therefore does not increase the verified-new operator count.

Overlap-weight associativity rejected at n=16 (impulse weights 8 versus 4).
Nonmultiplicative support extension rejected at n=12.
Binomial root products have local radius 1/q: their proposed half-plane
bridge was rejected even though their formal algebra is valid.

INTEGER SIZE GRAMMAR AND A PAIRED ROOT BRIDGE
Kernel programs scored: {size['kernel_grammar']['programs_scored']}.
Training fits: {size['kernel_grammar']['training_fits']}; fresh finite survivors:
{size['kernel_grammar']['held_out_survivors']}. The {size['kernel_grammar']['distinct_finite_basis_fingerprints']} finite fingerprints are not
verified operator counts. Selected floor/ceiling kernels have universal
cocycle proofs, and an independent implementation passes every gate:
{size_check['all_passed']}. The additive gcd expression recovers unitary
convolution. Shifted coprimality and a mistyped additive residue carry fail.
Floor-quotient transfers collapse to ordinary LOG above a proved cutoff.

Let h_b(n)=floor(log_b(n)), H_b(n)=ceil(log_b(n)), computed exactly.
Kfloor selects h_b(a*b)=h_b(a)+h_b(b); Kceil selects the ceiling equality.
Each is associative and unital; its complementary carry-only product is
associative without a unit. They change under relabeling actual prime
values, but still generalize to monoids with assigned multiplicative sizes.
The two U=EXP_K LOG_D transfers have exact inverses and q-root limits.
Every finite q zeta lift and its limit has coefficients in [0,1], proving
absolute convergence and locally uniform limits on Re(s)>1.

For g=f^beta and R_b keeping the coefficients at b^k, the universal law is
  1/2*(g Kfloor g+g Kceil g-g*g+R_b(g*g))=g*R_b(g).
The zeta paired series is zeta^beta*R_(b,beta), initially Re(s)>1.
A beta-moment proof gives, for EVERY b>=2 and beta in [0,1],
  Re R_(b,beta)(s)>=1/(1+b^-Re(s))>1/2 on Re(s)>0.
This holds even for composite bases, where R_b itself is not an ordinary
algebra homomorphism. The correction uses classical hypergeometric functions.

RH iff all pole-cancelled dyadic paired roots continue single-valuedly and
holomorphically to Re(s)>1/2. Any fixed irrational beta in (0,1) also gives
that criterion; the implemented scalar grammar remains rational. Neither
criterion proves the required continuation or a new estimate about zeros.

Six fresh actual-zeta points each pass the paired-root formula and a
separate floor-square formula using vertically shifted zeta roots. Both
have explicit infinite tails. Omitting the essential b-power resonance
term is rejected at every point. An independent verifier uses ordinary
Fourier sums instead of Fejer means, different cutoffs, and a rational
ratio series instead of native hypergeometric evaluation: all passed=
{size_analytic_check['all_passed']}. At the certified actual simple critical
zero, twelve paired correction cases stay nonzero; nine fractional cases
detect monodromy, and three integer-parameter cases correctly have no
branch obstruction. This boundary test is compatible with RH.
The Fourier identity is proved on Re(s)>1 and its quantitative error
bound on Re(s)>2. A subsequent regularity audit rejects individual
finite-power half-plane holomorphy, as detailed below. The paired
composition is a consequence, not another
primitive counted by naming a macro. Historical novelty remains unresolved.

ARTIFICIAL RESONANCE AND THE INFINITE ROOT-LIMIT OBSTRUCTION
Volume models scored: {size_resonance['volume_grammar']['models_scored']}; training fits:
{len(size_resonance['volume_grammar']['training_fits'])}; fresh survivors:
{len(size_resonance['volume_grammar']['survivors'])} syntactic aliases for the single law 1/q!.
For every finite q>=2, every b>=2, and every nonzero integer m, the
individual size lift has a nonzero Abelian singularity at
  s=1+2*pi*i*m/log(b).
For alpha=1 the floor coefficient is
  -sum_(r=1)^(q-1) (1/(2*pi*i*m))^r/(q-r)!,
and the ceiling coefficient is its conjugate. The universal proof uses
positive circle measures from genuine zeta root coefficients, not a
finite fit or an assumption about the zeros. These singularities would
occur independently of RH, so they cannot serve as off-line-zero evidence.

Twenty-seven actual-zeta/Hurwitz controls certify the opposite floor/ceiling
q=2 residues and zero-free actual-zeta neighbourhoods. The independent
verifier changes the Hurwitz tail, computes zeta derivatives from finite
arithmetic Euler-Maclaurin sums, and uses a Cauchy zero-free bound. All
{len(size_resonance_check['checks'])}/{len(size_resonance_check['checks'])} independent gates pass.
These controls are separate from the {bridge_count} arithmetic-to-zeta
comparison cases; they are not added to that count.

The infinite root-order transfer has a different obstruction at s=1:
  U(1+epsilon)/log(1/epsilon)^N -> infinity for every fixed N>=0,
  epsilon^a*U(1+epsilon) -> 0 for every fixed a>0.
This rules out every finite real-power pole cancellation producing a
holomorphic germ at 1. The finite-q residue 1/q! and epsilon*U both tend
to zero; vanishing Abelian residues do not imply regularity. Nine actual-zeta
log-angle cases include rigorously anchored branches and positive infinite
series lower bounds; a second checker recomputes all branches and bounds.
The uniform-angle Bessel model is classical and is not claimed as an
asymptotic for actual U. The previously proved paired root law survives;
the individual RH regularity criterion is rejected. General continuation
with additional singularity subtractions remains unestablished.

TWO SIZE CONSTRAINTS: A PROVED NATURAL BOUNDARY
Boolean programs scored: {joint['boolean_grammar']['models_scored']}; training fits:
{joint['boolean_grammar']['training_fits']}; fresh finite survivors:
{joint['boolean_grammar']['held_out_survivors']}. Their four truth tables are AND,
the first kernel, the second kernel, and the constant-one kernel. These
are established closure rules, not 80 new operators. Intersections retain
the generic inverse and normalized group laws. The complement need not
be associative: bases 2,3 give a counterexample at (2,3,6).

The empirical {joint['correlated_angle_volume_grammar']['models_scored']}-program volume grammar leaves one law:
  independent bases: 1/(q!)^2;
  c=b^k: binomial(k+q-1,q)/(k^q*q!).
In particular, bases 2,4 give 3/8 at q=2, whereas independent bases give
1/4. Exact box counts, 24 generic records and 27 sparse large-integer
bivariate cycle profiles pass an independent divisor-oriented audit.

For independent b,c, every alpha>0 and finite q>=2,
  epsilon^alpha*L_q(1+epsilon+i*(m*tau_b+n*tau_c))
       -> A_q(m)*A_q(n),
with every coefficient nonzero. The frequency group is dense, proving
that Re(s)=1 is a natural boundary, even for meromorphic continuation.
This filter-created obstruction is unconditional; it is not evidence of
off-line zeta zeros. Dependent bases and infinite root order are excluded
from this specific theorem, and no many-reciprocal-log independence is
assumed. The separate paired single-base root law remains valid.

Six fresh actual-zeta comparison cases pass Fejer error bounds. An
independent evaluator recomputes coefficients through 768, replaces
Fejer sums with ordinary Fourier sums, uses elementary even-part root
resonances, and rejects a smaller coefficient perturbation at every
point. Independent analytic gates: {len(joint_analytic_check['checks'])}/{len(joint_analytic_check['checks'])} passed.
The {len(joint_analytic['actual_root_torus_moment_controls']['independent_records'])} actual-root torus cases and
{len(joint_analytic['actual_root_torus_moment_controls']['dependent_records'])} correlated zero-frequency controls are separate from the
{bridge_count} arithmetic-to-zeta comparison count. For bases 2,4 the
common-power projection is R_4: omitting it changes the exact n=4
coefficient from 3/4 to 5/16. Historical originality remains unresolved.

SIGNED CANCELLATION: UNIQUE q=2 SURVIVOR, KNOWN PROJECTION REDUCTION
Programs scored: {cancellation['frequency_grammar']['models_scored']}; single-mode training fits:
{cancellation['frequency_grammar']['training_fits']}; fresh survivors:
{len(cancellation['frequency_grammar']['survivors'])}. Among nonzero rational vectors, only q=2 and equal weights cancel every nonconstant
Abelian mode. The universal proof applies to all rational vectors, not
just the enumerated coefficient range. At q>=3 every nonzero rational
constant combination has dense surviving modes and a natural boundary
on Re(s)=1 for independent bases. This statement excludes averaged-kernel
lifts, dependent bases, variable weights and infinite root order.

The exact bilinear grammar learns ten coefficients from
{cancellation['bilinear_projection_identity']['exact_training_equations']} equations on unrelated input pairs:
  (1,1,1,-1,-1,1,1,-1,-1,1).
Expansion of the power-index indicators proves the universal identity.
Isolating three projection terms yields the normalized corrected root
  W=g*(R_b(g)+R_c(g)+R_bc(g))/3, g=f^beta.
Its zeta correction is holomorphic and nonzero on Re(s)>0 for every
beta in [0,1], by a positive Hausdorff-moment lower bound. All pole-cancelled
dyadic W roots give an RH-equivalent continuation criterion, but no new
RH estimate. The operation is a known composite after this reduction.

Averaging remains a separate type gate. Prime-base average kernels are
classical weighted transports; bases 4,8 fail associativity at (2,2,3).
Even for prime bases, averaging four q-fold lifts is not a q-fold lift
in the average kernel: q=3,n=8 gives 20/27 versus 3/4. Common powers for
bases 4,8 are 64^k; choosing the larger original base is incorrect.

Six fresh zeta comparison cases, each with two representations, pass at
Re(s)=3/2,7/4,2 with explicit infinite tails and coefficient perturbations.
The independent checker changes the coefficient cutoff to 6144, replaces
native hypergeometric resonances by exact ratios, and verifies smaller
perturbations. Independent exact gates: {len(cancellation_check['checks'])}/{len(cancellation_check['checks'])}; analytic gates:
{len(cancellation_analytic_check['checks'])}/{len(cancellation_analytic_check['checks'])} passed.

A Hardy-Z scan locates a fresh zero near 21.022039638771555i. Direct Arb
Taylor-Rouche comparison certifies one simple zero in a radius-1/100000
critical-line disk; the independent checker uses a larger Cauchy circle.
Nine correction controls include six nontrivial fractional branch jumps
and three correct integer-phase controls. These are boundary-zero controls,
compatible with RH and separate from the {bridge_count} comparison-case count.
The verified-new operator list remains empty. The corrected survivor is
a known composite; historical originality of the signed-domain consequence
remains unresolved.

MIXED ADDITIVE / DIVISOR INDICES: PRIME-BINARY PARTITIONS
Normalization programs scored: {mixed_index['normalization_grammar']['models_scored']}.
Recurrence programs scored: {mixed_index['parity_recurrence_grammar']['models_scored']}; training fits:
{mixed_index['parity_recurrence_grammar']['training_fit_count']}; fresh survivors:
{len(mixed_index['parity_recurrence_grammar']['survivors'])}.
The selected operation is N_beta=M EXP_C(beta LOG_D), where C splits the
bits of n-1 without carry and M divides by popcount(n-1)!. For even n,
  F_beta(n)=sum_(r=1)^v2(n) beta/r*(k-r)!/k!*F_beta(n-2^r+1).
The learned identity is proved by the unique partition block containing
bit zero: its value plus one is an even prime power, hence 2^r. The
independent anchored-partition implementation changes the production
Euler recursion and passes {len(mixed_index_check['checks'])}/{len(mixed_index_check['checks'])} exact gates.
Actual prime labels matter: F_1(7)=1, F_1(11)=3/4 despite equal bit counts.

An entire Bell-polynomial majorant proves absolute and locally uniform
zeta-input convergence on Re(s)>0 for every complex beta, jointly entire
in beta. For real beta in [0,1], the normalized q-fold carry-free lifts
of ordinary zeta^(beta/q) converge locally uniformly there as q tends
to infinity. The corresponding generic B roots are exact, but B is a
different product: at n=6, N_(1/2)(u)=1/8 while the ordinary D half-root
of N_1(u) has coefficient zero.

The six fresh native-zeta input cases uniquely recover exact LOG(zeta)
coefficients through 64 at real part 2048, without supplied prime-power
locations. Independently, real part 1024 recovers through 128; arithmetic
cutoffs double to 2048 and exact Bell-row tails replace geometric tails.
This is explicitly a coefficient-origin bridge for N. The reverse
calibration V=EXP_D LOG_A has direct scalar representations via shifted
zeta sums and one zeta value plus an arithmetic correction. Both operations
reject the smaller independent coefficient perturbation at every point;
{len(mixed_index_analytic_check['checks'])}/{len(mixed_index_analytic_check['checks'])} independent analytic gates pass.

Two new operator controls reuse the existing simple-zeta-zero disks near
14.13473i and 21.02204i. N is proved holomorphic across both, without
claiming a converged numerical N value there. V is certified nonzero on
both full disks. Consequently formal group invertibility and typed root
regularity do not preserve the ordinary zeta root obstruction. No new
RH estimate is proved. The unnormalized additive EXP_A LOG_D control
has no convergent Dirichlet half-plane at all. These type/domain controls
are separate from the {bridge_count} comparison-case count.
Subset convolution, Bell partitions and formal LOG/EXP are classical;
publication history of the specific prime-binary application is unresolved.
The verified-historically-new operator list remains empty.

QUADRATIC INDEX DIFFERENCES: ORDINARY ROOTS RETAINED
Weight programs: {difference['finite_difference_calibration']['models_scored']}; training fits:
{difference['finite_difference_calibration']['training_fits']}; fresh survivors: 1, the known third forward difference.
Order programs: {difference['cancellation_order_grammar']['models_scored']}; training fits:
{difference['cancellation_order_grammar']['training_fits']}; fresh survivors: 1, r=m*(2^k-1).
Leading recurrence programs: {difference['leading_recurrence_grammar']['models_scored']}; training fits:
{difference['leading_recurrence_grammar']['training_fits']}; fresh survivors: 1.
Thirty-nine exact profiles are independently recomputed by Newton interpolation
and separate logarithm/exponential recursions. The formal operation
  P_(m,k,beta)=EXP_D(beta*(I+A_m^k)*LOG_D)
uses augmentation pushforwards n->n(n+a). Its exact group and fractional
root laws use ordinary Dirichlet convolution. A sparse inverse control
through 10^8 rejects stopping after the first resolvent correction.

For zeta input H_beta=zeta^beta*exp(beta*Delta), initially Re(s)>1.
The universal cancellation law gives a holomorphic grouped Delta on
  Re(s)>-m+(m+1)/2^k.
For m=2,k=2 this is Re(s)>-5/4. The correction is zero-free there, so
ordinary zeros and their multiplicities are retained. The negative-domain
statement is not ordinary coefficient-series convergence: the terms at
p^(2^k), p>m, do not tend to zero when Re(s)<=0.

Six fresh direct scalar comparisons pass with coefficient cutoff 4096,
native shifted-log-zeta sums and proved tails. Independently, cutoff 6144
uses one native zeta root and grouped prime-power corrections, with changed
bounds and a smaller coefficient perturbation. Two additional negative-domain
grouped controls are separate from the {bridge_count} comparison-case count.
Independent exact gates: {len(difference_check['checks'])}/{len(difference_check['checks'])}; analytic gates:
{len(difference_analytic_check['checks'])}/{len(difference_analytic_check['checks'])} passed.

New correction tests across both existing critical-line zero disks preserve
fractional root monodromy and the correct trivial integer phase. The higher
m=6,k=1 instance also covers the actual trivial zero -2, certified simple
by Taylor/Rouche and independently by the functional equation/Cauchy bound.
Its correction equals exactly one at -2; the transformed integer-power
function has the same derivative there. Native-centre/derivative enclosures
and independent grouped/integral bounds cover the whole zero disks.
Explicit native coefficient lists and leading-coefficient checks prevent
scalar tuple interpretation from passing a vanished-coefficient test.

Finite differences and formal LOG/EXP are classical. Publication history
of this particular quadratic-iteration application remains unresolved.
The operator has a verified ordinary-root bridge, but no new estimate
establishing RH; the historically-new operator list remains empty.

NONLINEAR PRIME-SUM LOG COUPLINGS: ROOT GATE BROADENED
Homogeneity programs: {pair['universal_root_constraint_grammar']['models_scored']}; training fits:
{pair['universal_root_constraint_grammar']['training_fits']}; surviving linear scalars: {len(pair['universal_root_constraint_grammar']['survivors'])}.
The universal theorem says a coefficient-local polynomial map commuting
with every input half-root must be EXP_D L LOG_D with linear L. Requiring
that law would preclude nonlinear LOG candidates before numerical testing.
The broadened grammar therefore retains ordinary-zeta zero controls while
allowing a measured input/output-root anomaly.

The selected map is P_r(f)=EXP_D(g+K_r(g,g)), g=LOG_D(f), with
K sending two indices to xy(x+y)^r. It has a coefficient-triangular inverse;
its bilinear graft is generally nonassociative and P is not a D group
homomorphism. The input-root amplitude is beta^2; the output-root amplitude
is beta. Their quotient is EXP_D(beta*(beta-1)*K_r(g,g)). Amplitude programs:
{pair['input_root_amplitude_grammar']['models_scored']}; training fits: {pair['input_root_amplitude_grammar']['training_fits']}; fresh survivor: 1.
Inverse-mass programs: {pair['inverse_mass_recurrence_grammar']['models_scored']}; training fits:
{pair['inverse_mass_recurrence_grammar']['training_fits']}; fresh survivor: 1, the classical Catalan recurrence.
Independent ordered trees reproduce all inverse masses and actual labels
through six leaves. The r=0 scalar square-root inverse is a known calibration.

For r>=1 the odd-index quotient is fixed on EVERY input. On actual zeta,
P_3(u)(256)=2 while P_3(u)(6561)=1; swapping primes 2,3 therefore changes
the operator. Generic impulse and nonassociativity controls agree.
It is also nonmultiplicative on zeta input: coefficient 750 is 3, while
the coefficients at its coprime factors 2 and 375 are both 1.
Seven independent exact gates pass, including the new odd-quotient gate.

For zeta input the correction Gamma_r has a genuinely convergent ordinary
Dirichlet series on Re(s)>2/(r+2). This is a sufficient domain, not a
maximal-domain classification. The least r whose AM-GM certificate crosses
the critical line is r=3, giving Re(s)>2/5. Both scalar root families equal
zeta^beta times a holomorphic nonzero correction there. At beta=1 all
ordinary zeta zeros and their multiplicities are preserved in that domain.

Six fresh full-series cases pass with native zeta Mellin--Barnes integrals,
explicit contour tails and coefficient cutoff 4096. Independent checks use
a grouped prime-power double sum, changed square/full cutoffs 80/6144,
changed tails and smaller coefficient perturbations. A separate native
beta integral checks the classical contour normalization. All five
independent analytic gates pass. Incorrect contour factors and first-kernel
coefficient perturbations are rejected separately from the full-series errors.

Twelve root-correction controls on both existing simple-zero disks preserve
fractional phases and the correct zero integer phase, with two independent
whole-disk zero-free majorants. The native centre integrals use small initial
segments to avoid nonfinite wide logarithm enclosures. The r=0 log-square
composite has nonconstant correction monodromy and fails this zero-sensitive
gate. The phase-factor bounds omit the additional vanishing zeta^beta
factor, as explicitly recorded. These zero controls are separate from the
{bridge_count} comparison-case count. Catalan trees, Tornheim denominators,
beta Mellin inversion and formal LOG/EXP are classical. No historical
originality or new RH estimate is claimed.

PRIME-SUM SECTOR DECODER: ZERO OBSTRUCTION AND SHARP DOMAIN LOSS
Decoder programs: {decode['decoder_grammar']['models_scored']}; training fits:
{decode['decoder_grammar']['training_fits']}; fresh survivor: 1, full exponent valuations modulo 3.
The unrestricted integer probe has {fibres['integer_input_probe']['collision_count']} collisions. Collision-free
bounded prime-power samples are not treated as a global injectivity proof.
The universal theorem instead isolates outputs with exactly two nonzero
prime exponent residues modulo r. Their prime-power input fibre is unique.

D_r is a linear partial coordinate permutation with encoder E_r and two
idempotent projection inverse laws. It decodes the prime-power-supported
bilinear graft to the r-filtered D product minus its same-prime diagonal.
All {len(decode['zeta_decoded_profile']['queries'])} zeta-derived coefficient queries through {decode['zeta_decoded_profile']['decoded_cutoff']} pass independent
complete integer-sum/discriminant enumeration. The source first enumerates
the full bounded prime-power graft without sector prefiltering. Missing
encoded prefix coordinates are not substituted by zero. A large held-out
integer exposes repeated native factor entries; summed exponents and exact
product reconstruction now pass the independent regression.

The decoded scalar identity is T_r=G_r^2-Q_r, where
G_r=LOG zeta(s)-LOG zeta(r*s)/r and Q_r is the prime-local square diagonal.
Its ordinary series has exact absolute abscissa 1. Q_r is holomorphic on
Re(s)>1/2 and locally extends as LOG zeta(2s)+B_r, B_r holomorphic on
Re(s)>1/3. Six fresh native-zeta cases pass with source Mobius/prime-zeta
references and explicit tails. The independent route changes the decoded
cutoff from 4096 to 6144, uses prime-local Euler logs, and rejects smaller
coefficient errors. All eight exact and four analytic gates pass.

At both reused actual simple-zero disks, encoded Gamma_3 is holomorphic,
but decoded T_3 has a nonzero jump 4*pi*i*G_3-4*pi^2. Branch-independent
source lower bounds are about 117.7468 and 145.5973; independent Taylor/
Cauchy bounds give 108.0995 and 138.4536. These are decoded-log jumps,
separate from full zeta-root jumps and from the {bridge_count} comparison count.

The sharp norm law explains the analytic loss: for sigma>0,
D_r:A_sigma->A_tau is bounded iff tau>=(r+1)*sigma, with exact norm
6^(sigma-tau)*5^(r*sigma). Pure power weights multiply by n^(-lambda)
and shift T_r to T_r(s+lambda). Using the available encoded norms and
target tau=1/2 originally forced lambda>(3*r+2)/(2*(r+2)); at r=3, lambda>11/10
and the critical-zero obstruction moves to real part<-3/5. This concerns
this decoder and these weights, not all possible RH approaches. The later
full endpoint theorem below permits equality but retains the domain loss.

On raw zeta coefficients D_r is only a known two-prime mask. Prime
valuations, coordinate projections, Mobius inversion and logarithmic
zero branching are classical. Originality of the particular decoder
application and norm tradeoff remains unresolved. The pole-cancelled
continuation criterion is RH-equivalent but supplies no new RH estimate.

FULL PRIME-PAIR DECODING: CLASSICAL CALIBRATION AND SHARP HILBERT LOSS
The universal prime-pair extension includes diagonal pairs. Every prime-pair
image has a unique fibre among ALL prime-power inputs, without asserting
global prime-power injectivity. Its {prime_pair['prime_pair_decoder_grammar']['models_scored']}-program grammar leaves one survivor;
five training fits are reduced by the held-out p=2 diagonal and large primes.
All {prime_pair_check['exact_zeta_audit']['complete_prime_power_fibres_checked']} zeta-derived queries, including {prime_pair_check['exact_zeta_audit']['diagonal_queries']} diagonals, pass complete integer
sum/discriminant checks. Independent sieve/convolution and semiprime-degree
calculations confirm the arrays. Six independent exact gates pass.

For unrelated prime-supported inputs, product decoding B_r K_r recovers
ordinary Dirichlet convolution; sum decoding A_r K_r recovers ordinary
additive convolution. On the zeta-derived graft these are P(s)^2 and
Z_+(s)=sum_(p,q primes)(p+q)^(-s). They are KNOWN operators/counts, adding
a verified consequence of the ninth family, not a tenth new primitive.
On raw zeta coefficients the outputs also reduce to known masks/counts.
The additive decoder has a nonzero kernel delta_21000-delta_25000 at r=3,
so it has no two-sided inverse. Missing encoded prefix data is not zero.

Six fresh comparison groups check BOTH scalar functions with actual native
zeta. Additive references use centered beta Mellin inversion of prime zeta,
with finite Mobius-polynomial integration, a gamma L1 approximation bound
and an explicit infinite contour tail. Source cutoffs are 2048/8192.
Wide initial intervals returned finite but insufficiently narrow balls;
short starting segments repair only failed cases, retaining passed cases
with a coefficient digest. The failed initial record is archived.
Independent checks use a prime square through 512, changed infinite tails,
cutoffs 3072/12288 and smaller errors. A beta-only kernel integral rejects
a factor-two error. All four independent analytic gates pass.

The PRIME-ONLY encoded component has exact absolute abscissa 2/(r+2),
with absolute convergence at its endpoint, by unconditional prime density.
The additive output has exact abscissa 2 and converges absolutely at 2;
the product output has exact abscissa 1 and diverges at 1. No pointwise
Goldbach hypothesis is used, and endpoint convergence is not a claim
of maximal analytic continuation.

Sharp l1 decoder thresholds are tau>=(r+2)*sigma for sums and
tau>=(r+1)*sigma for products. Exact bounded norms are respectively
2^((2r+2)*sigma-2*tau) and 4^((r+1)*sigma-tau). The prime-only endpoint
allows equality in its pure-power regularization thresholds: lambda>=3/2
for sums at target 1/2, and lambda>=(3r+2)/(2*(r+2)) for products.
These are generic operator bounds; the special product series already
has the better ordinary abscissa one. This stage's proof was prime-only;
the full prime-power endpoint is now independently proved below.

In weighted Hilbert spaces the additive map is bounded iff
tau>=(r+2)*sigma+1/2, sigma>=0. Its exact norm squared is the supremum
of weighted prime-pair row sums. The boundary upper bound is
2^(-2*sigma-1/2); no exact infinite maximum is inferred from a finite prefix.
PNT averaging supplies the necessity proof, so even unweighted l2
boundedness is rejected. Increasing the encoding power cannot remove
these generic domain losses.

The PRODUCT output restores prime-zeta-square monodromy at both reused
simple-zeta-zero disks, with native modulus and changed Taylor/Cauchy
certificates. The encoded prime-only component is holomorphic across
each disk. Values or monodromy of the ADDITIVE output at those zeros
are not inferred. The reviewed prior Goldbach continuation paper uses
von Mangoldt weights, so its conditional theorems are not borrowed for
this unweighted prime-only scalar function. Classical primitives are
rediscovered; precise application/norm originality and a new RH estimate
remain unresolved. The {bridge_count} comparison groups retain separate auxiliary
zero and normalization controls.

RESIDUE-VISIBLE PRODUCT DECODING: SAME-PRIME CANCELLATION AND LIMIT
The tenth mathematically verified family is a linear aggregating decoder.
It adds admissible same-prime inputs to the earlier two-visible-prime
sector. An oversized full visible factor U satisfies U^(r+1)>N for the
same-prime sector, while every competing distinct-base PP fibre has the
opposite inequality. This supplies a universal complete-fibre uniqueness
proof on the accepted sectors, without assuming global PP injectivity.
The classifier grammar scores {visible['single_visible_classifier_grammar']['models_scored']} comparisons, with three training fits and
one held-out survivor. The reconstruction grammar scores
{visible['same_prime_reconstruction_grammar']['models_scored']} programs, with five training fits and one survivor including two-prime diagonals.

V_r K_r(a,b) is the filtered ordinary Dirichlet product for arbitrary
prime-power-supported inputs. Same-prime total exponents and cross-prime
individual exponents must be nonzero modulo r. All
{visible_check['exact_zeta_audit']['complete_prime_power_fibre_queries']} complete PP-fibre queries, including
{visible_check['exact_zeta_audit']['same_prime_queries']} same-prime queries, pass the independent sum/discriminant audit.
Exact zeta profiles r=3,4,5,7,11,13 extend through 8192. Their first defect
from the ordinary logarithm square is at 2^r with coefficient -2H_(r-1)/r.
The 35-program order grammar and 54-program harmonic grammar recover that
law, which is classical Stirling/harmonic arithmetic, not a new primitive.

The scalar identity is
U_r=(LOG zeta(s)-LOG zeta(r*s)/r)^2+R_r,
where the local R_r coefficients vanish below degree r and have modulus
at most one. Hence R_r is single-valued holomorphic on Re(s)>1/r;
for r=3 the cancellation improves the separate diagonal domain to Re(s)>1/3.
The ordinary full U_r series still has exact absolute abscissa 1.
R_r is ADDITIVE, not a claimed zero-free multiplicative factor.

Six fresh full scalar groups compare native zeta references with exact
decoded prefixes. The checker changes the cutoff from 8192 to 12288,
uses prime-local root-of-unity filtering and rejects smaller errors.
Six separate correction-only cases at real parts 3/8,2/5,5/12 pass both
routes, using leading prime-zeta subtraction, changed cutoffs and explicit
infinite tails. These are auxiliary controls, separate from the cumulative
{bridge_count} full comparison groups. All six exact and six analytic gates pass.

At the two reused simple-zero disks, eight parameter controls r=3,4,5,7
retain the nonzero quadratic-log jump. The independent Taylor/Cauchy
certificate uses radius 1/48; no zeta(2s)-nonzero gate is required.
For multiplicity m, the jump differs from that of (LOG zeta)^2 by exactly
-4*pi*i*m*LOG zeta(r*s)/r. Its height-independent bound
(4*pi*m/r)*LOG zeta(r*sigma) decreases exponentially with r. On a chosen
zero-free, pole-free LOG branch, U_r itself tends locally uniformly to
(LOG zeta)^2, with a written exponential majorant and changed-point checks.
The pole-cancelled global continuation criterion remains RH-equivalent;
neither these local estimates nor the numerical controls establish it.

The decoder aggregates floor(k/2) coordinates at eligible p^k, has kernel
delta_16000-delta_8192 at r=3, and is unbounded on unweighted l2. For
sigma>0, both A_sigma->A_tau and H_sigma->H_tau are bounded iff
tau>=(r+1)*sigma. The absolute norm is exactly 4^((r+1)*sigma-tau),
as is the Hilbert norm under the additional condition r*sigma>=1.
Exact low-weight rows reject the unqualified norm-one assertion.
Hilbert weights are coefficient norms; unlike absolute weights they do not
directly identify pointwise Dirichlet half-planes. No spectral RH criterion
is inferred from the Hilbert calculation.

The FULL weighted prime-power source now has exact absolute abscissa
2/(r+2), WITH endpoint convergence. The proof uses the unconditional count
W(X)=sum_(p^e<=X)1/e=O(X/log X). Endpoint absolute norms decrease with r
and are uniformly at most Gamma_3(2/5), a proved finite quantity not
numerically evaluated here. Endpoint decoding has exact norm one, but
its bounded target weight is 2(r+1)/(r+2)>=8/5 and tends to 2.
This closes the earlier full-source endpoint gap while preserving the
critical-line domain loss. Pure power damping at r=3 now permits
lambda=11/10; the critical obstruction is still shifted to real part<=-3/5.

Raw-zeta actions give known partition masks, and root-of-unity filters,
harmonic coefficients, prime-zeta inversion and PNT are classical.
The particular arithmetic application and combined estimates have unresolved
historical originality. Verified-historically-new operators remain zero;
no new RH estimate is proved. Proof: visible_proof.txt; data: visible-results/.

GAP CORRELATION: SHARP CRITICAL ENDPOINT AND ORDINARY ROOTS
The grammar now also sends distinct indices a,b to ab|a-b|^r, r>=1.
The logarithmic EXP map has an exact triangular inverse and quadratic
root anomaly, but is not an ordinary group homomorphism. The zero gap
is excluded, and the index product is nonassociative. Known bilinear
additive correlation is positively rediscovered with signed rational inputs.
The detector retains ten candidate families and records a sixteenth
compound consequence; this known-kernel extension is not another primitive.

The 27-program inverse-mass grammar fits the first two-seed profiles but
fails at four leaves on held-out collision seeds 2,3,5. Exact mass is 232
rather than 240. The universal recurrence subtracts actual equal-index
overlaps. Global PP injectivity already fails at r=1,index=30, with pairs
(2,5),(3,5); the complete integer fibre also contains (5,6).
The independent difference/discriminant checker verifies all 40955
encoded indices across five zeta prefixes through 8192, plus twelve
finite prime-density certificates and a native-Arb finite FFT comparison.

Writing g=Lambda/log and Gamma^-_r for the encoded zeta-log pair sum,
Gamma^-_r=2*sum_d d^(-rs)*sum_n g(n)g(n+d)/(n(n+d))^s.
The exact absolute abscissa is max(2/(r+2),1/2). Bulk separated primes
give the first threshold; Cauchy averaging of near pairs from PNT gives
the second without a fixed-gap conjecture. A layer-cake lower bound proves
divergence at the r=2 critical endpoint. For r=1 and r>=3 the endpoint
converges, using unconditional Brun--Titchmarsh and uniform prime-pair
sieve bounds. r=3 is the first integer giving a correction continuous
on Re(s)>=1/2 and holomorphic on Re(s)>1/2.
The FFT exploration extends PP inputs through 524288, but is not an
infinite certificate. The 220-program threshold grammar fits explicit
index/dimension predictions, not independently certified infinite data.

Ordinary input roots equal zeta^beta*exp(beta^2*Gamma); output roots use
amplitude beta. Their full positive-beta ordinary series still has
absolute abscissa 1. At a critical-line zero of multiplicity m, the
finite nonzero correction gives exponent m*beta when approaching from
the right. Whole zero-disk correction holomorphy is NOT established.
All pole-cancelled dyadic roots give an RH-equivalent continuation
criterion, but no new estimate establishing that continuation is proved.

Six fresh full native-zeta groups pass encoded sums against anchored
NONCONJUGATING polynomial correlations. The independent route changes
the PP cutoffs 1024/2048 to 1536/3072, uses direct pairs and zeta(s),zeta(4s)
anchors, and replaces native-zeta tails by integer-integral bounds.
Both reject deliberate errors at index six and Hermitian conjugation;
the source also rejects an included diagonal. The cumulative full scalar
comparison count is {bridge_count}. Five ordinary-root scalar groups and six
one-sided zero groups on the two reused simple-zero disks are separate.
The latter have three positive input-root factor bounds each, and an
independent Cauchy check; no additional zeta zero is located in this stage.
All six exact and six analytic gates pass.

Toeplitz/Young bounds give |Gamma|<=2*zeta(r*sigma)*LOG zeta(2*sigma)
strictly right of the critical line, but the source l2 norm diverges at
the line. The endpoint requires extra arithmetic sparsity. The zero-
diagonal kernel is indefinite: delta_2-delta_3 gives coefficient -2 at six.
There is no positive spectral RH operator established by these checks.
Prime-pair correlation is known prior mathematics; history of this precise
weighted compound application remains unresolved. No historically-new
operator or zero-location estimate is claimed. Proof: gap_proof.txt;
data: gap-results/; figure: gap-results/gap_overview.png and .pdf.

PRIME GAP-LAPLACIAN: CLOSED SHEAR INVERSE AND PAIRED CANCELLATION
The three index images are p^2*(q-p)^r, p*q*(q-p)^r, q^2*(q-p)^r,
with learned weights 1,-2,1 and p<q PRIME. The 49-program completion
grammar positively recovers known second-difference/Laplacian weights.
Every correction output is composite, so its prime projection vanishes.
In logarithmic coordinates this gives S_t S_u=S_(t+u), with exact inverse
S_(-t). Input roots have correction amplitude t*beta^2 and output roots
t*beta. This is not an ordinary unit-group homomorphism.

The support grammar also finds the valid odd-input closure. Prime-power,
squarefree, Omega<=2 and even masks fail complete sparse composition.
The even mask initially passed a prefix through 2048; its actual first
failure is 59105344. The failed prefix is archived, and source/checker
now recompute full sparse compositions. Only the failed mask search was
replaced; the other passed exact records were retained.

For even r, diagonal images are squares and negative cross images are
nonsquares with squarefree part p*q. This proves sign separation and a
complete universal prime-fibre rule. The independent checker verifies
32764 encoded indices through 8192 across r=2,4,6,8, plus generic exact
root/group/inverse laws with Omega-derived EXP/LOG. All five exact gates pass.

H_r=sum_(p<q)(q-p)^(-rs)*(p^-s-q^-s)^2 has paired absolute convergence
and holomorphy on Re(s)>2/(r+2), r>=3, with convergence at that endpoint.
Derivative cancellation and PNT prove this without a prime-pair conjecture.
For r=4 the grouped correction domain is Re(s)>1/3. Its ORDINARY arithmetic
coefficient absolute edge is instead 1/2, with endpoint convergence;
the coefficient proof uses sign separation and the uniform sieve upper
bound for balanced prime pairs. Splitting the paired sum into three
infinite sums below one half is invalid. The full positive-beta transformed
ordinary series still has exact absolute abscissa one.

The sharp same-weight bilinear norm is
((3/2)^sigma+(2/3)^sigma+2)/2, attained on delta_2,delta_3.
The prime-zeta input norm diverges for sigma<=1, so this generic estimate
does not supply critical-strip zeta bounds. Real graph energy is positive,
but its Hermitian extension depends on s and its conjugate. All six fresh
full native-zeta groups reject substituting it for holomorphic H.
No zero spectrum, determinant identity or positive spectral RH model follows.

Six full scalar groups compare exact signed EXP coefficients with
zeta(s)^beta*exp(amplitude*H_4). The native reference restores prime-two
tails through prime zeta at 4s+k,5s+k,6s+k. The independent route changes
coefficient cutoffs 4096/6144, graph cutoffs 1024/1536, binomial degree
8/10, Mobius cutoff 32/40 and infinite tail bounds. A NONNEGATIVE EXP
majorant supplies the signed coefficient tail; a total-minus-actual-prefix
argument would be invalid here. Smaller coefficient errors at four are
rejected. Five ordinary-root scalar groups are separate auxiliaries.

Two whole correction-disk controls reuse the existing simple zeta zeros.
Direct/polynomial graph references change from 2048 to 1536/3072, with
uniform integer tails. Native H modulus bounds are below 0.435 and 1.845;
independent bounds are below 0.357 and 1.674. Thus exp(beta^2*H) has strictly
positive whole-disk lower modulus bounds for beta=1,1/2,1/4.
Ordinary zeta multiplicities and fractional-root monodromy survive.
No new zero is located and the RH-equivalent continuation criterion is
not proved. All six analytic gates pass. The cumulative full comparison
count is {bridge_count}; auxiliary root/zero groups are separate.

This is the seventeenth known-kernel compound consequence, with ten
candidate families retained. Graph Laplacians, finite differences,
elementary shears, prime projections and LOG/EXP are classical. The
specific arithmetic application and combined bounds have unresolved
historical originality. Verified-historically-new operators remain zero;
the research objective stays active. Proof: laplacian_proof.txt;
data: laplacian-results/; figure: laplacian-results/laplacian_overview.png and .pdf.

HIGHER PRIME MOMENTS: UNIFORM HEIGHT AND ORDINARY ZETA ROOTS

The eighteenth known-kernel compound consequence expands the grammar to
m+1 multiplicative faces with exact moment annihilation. Two bounded
searches score 28,610 programs and recover the classical alternating
binomial weights; higher exact solves check orders 6,8,10,12,16. Prime
mask search scores six minimum-gap predicates at training/held-out prime
cutoffs 127/251, selecting gap>=2; 240 index-scale models uniquely recover
4*6^m, with held-out orders through 16. The selected universal laws are
proved separately from those finite fits. Prime
projection gives a closed shear group and inverse. Complete sparse
composition is checked without an encoded cutoff. Valuation residues
modulo m+2 decode 4,764 finite-prime-input indices; separate complete
zeta prefixes check every one of 16,382 encoded indices. The first
regularized image is 4*6^m, with the exact ordinary coefficient change
t*f(3)*f(5). Input roots scale by beta^2, independent of moment order.

With even m and gap power m+2, the correction is
R_m=sum_(p<q,q-p>=2)(q-p)^(-(m+2)s)*(p^-s-q^-s)^m.
Its ordinary coefficient series converges on Re(s)>1/m; paired
continuation has the larger domain Re(s)>1/(m+1). For m>=4,
|R_m(s)|<=C(sigma)*(6^-sigma+10^-sigma)^(m-4), independently of height.
The prime-parity majorant at sigma=1/2 is below 0.693425 and the
geometric ratio is 0.72447605648070... . At m=64 the correction factor
exp(R_m) differs from one by less than 2.770e-9 for ALL Re(s)>=1/2.
This is a relative factor bound, not a height-uniform absolute bound
on the full transformed zeta function. Its sharp uniform limit
threshold solves 6^-sigma+10^-sigma=1, sigma=0.340431844164982...;
the resonant prime edge 3/5 proves nondecay at the threshold.

Removing only the sole gap-one prime edge 2/3 is essential. Without
that arithmetic mask, every fixed coefficient tends to the identity
but the correction grows without bound at 1/2+i*pi/log(3/2). The
detector now rejects that invalid limit interchange with certified
dominant-edge and infinite-remainder bounds, not finite-prefix fitting.

Six fresh correction/factored native-zeta AUXILIARIES change input
prime cutoffs 256/512 to independent 192/384 polynomial correlations,
using changed integer tails and smaller wrong-coefficient controls.
They are not full transformed EXP coefficient-origin checks; the
cumulative full comparison count at that stage remains 138. Five ordinary
root scalar groups and eight whole-zero-disk/order groups are separate.
The disk controls reuse two old simple zeros, with beta=1,1/2,1/4.
The correction is now an ordinary absolutely convergent series on
the entire zero disks, and its nonzero factor preserves multiplicity
and fractional monodromy. Increasing cancellation order approaches
the original root branching rather than eliminating it.

All five exact and six analytic gates pass. Ten candidate families
remain, with zero verified historical novelties. Binomial finite
differences, graph p-energies and shear groups are known; originality
of the specific arithmetic encoding and bounds is unresolved. This
stage gives a critical-half-plane correction estimate and a precise
root-sensitive failure test, but no estimate excluding off-line zeros.
The research objective remains active. Proof: moment_proof.txt;
data: moment-results/; figure: moment-results/moment_overview.png and .pdf.

GLOBAL RADIX CARRY: COMPLETE BRANCH LADDERS AND ROOT LOCATION FIDELITY

The nineteenth known-kernel consequence extends global total-degree
carry to integer radix b>=2. Literal digitwise no-carry is associative
for every base. The tempting binomial-nondivisibility substitution works
for prime bases but fails at composite base four, with parenthesizations
1 and 0 at degree triple (1,1,2). Universal LOG/EXP gives a normalized
unit-group transfer and inverse. Its root law is typed in G_b.
Ordinary output roots differ: at index eight, radix three gives 1/6
for the transferred input half-root but -1/48 for the output half-root.

The graded polynomial grammar holds out unrelated higher-grade inputs
and recovers LOG degree b-1 for bases 2,3,4,5,7. A 49-model radix-degree
search selects b-1, with separate universal proofs. The leading
coefficient satisfies the exact self-similarity law
H_(b-1)(s)=F_(b,beta/b)(b*s). It has an ordinary absolutely convergent
series on Re(s)>1/b. For b>=3, beta in (0,1], and Re(s)>=1/2,
|H_(b-1)|>=2-zeta(b*Re(s))^(beta/b)>0 at EVERY height.
Radix three beta=1 has uniform lower bound greater than 0.6227.

The complete (b-1)-st branch difference is
(2*pi*i*m*beta)^(b-1)*H_(b-1) around an ordinary zeta zero of order m.
This cannot vanish in the critical right half-plane. For b=3 the test
uses F_2-2F_1+F_0. A controlled model proves that a single pointwise
first jump can vanish exactly despite nontrivial second difference.
Its coefficient functions are fixed from zeta: the model is a control
of the derived criterion, not a claimed transform of a substituted input.
The two old certified simple zeta-zero disks pass complete ladder tests
for beta=1,1/2,1/4, with whole-disk bounds and Euler-anchored LOG zeta(2s).
Their logarithmic branch information is retained; their fractional-root
multiplier is not the polynomial branch law of this transfer.

A continued F_(3,1) zero near 0.8726892587266+14.7200361075490i is certified
simple by Rouche on radius 1e-5. Native zeta is nonzero on the whole
containing rectangle, with modulus greater than 0.4895; the transform
of the ordinary input half-root also has modulus greater than 0.5972.
An independent grade-power/Lucas implementation changes the grade and
Mobius cutoffs, derivative quotient and outer Cauchy radius, certifying
the same zero on a nested radius-5e-6 disk. Tiled corridors anchor the
local principal LOG to the Euler-normalized series. The operator's
ordinary output half-root has spurious sign monodromy on this disk.
This zero belongs to the operator, not zeta. Strip values use proved
analytic continuation below the ordinary series' exact abscissa one.
The initial insufficient outer-bound certificate remains archived;
only positive-margin certificates are accepted.

Five independent exact gates check 40,950 encoded zeta coefficients.
Six independent analytic gates pass. Six new full coefficient-origin
native-zeta groups change ordinary prefixes 4096 to 6144, grade cutoffs,
Mobius cutoffs, tail formulas and wrong-coefficient controls. They bring
the then-current full comparison count to 144. Four leading
self-similarity groups and five ordinary-root values are auxiliaries.
The two ordinary zeta zeros are reused; no new ordinary zero is located.

Polynomial pole correction of Z=(s-1)*zeta(s) gives an RH-equivalent
single-valued holomorphic continuation criterion. That extension remains
unproved; the leading-coefficient estimate does not exclude off-line
zeros. Digit-carry potentials, formal LOG/EXP and graded nilpotence are
known frameworks. The regular convolution historically called ternary
has a different shared-prime kernel. The exact global-degree application,
scale recursion and complete ladder have unresolved historical novelty.
Ten candidate families remain and verified historical novelties remain
zero. The research objective stays active. Proof: radix_proof.txt;
data: radix-results/; figure: radix-results/radix_overview.png and .pdf.

ACTUAL PRIME INFORMATION ACROSS SCALES: PRIMARY RESEARCH PRIORITY

The twentieth known-framework consequence/calibration gives the detector
an explicit prime-information requirement. A candidate must specify
counts, weighted mass, gaps, correlations or residues, its scale parameters,
and a new consequence beyond reconstructing known prime data. Numeric
samples, all-X identities and uniform estimates are recorded separately.
The existing ten candidate families are retained and triaged for this
purpose; candidates with actual prime-value dependence receive priority
for a new distribution consequence. Radix-limit work is secondary.

The 42-program extraction grammar uniquely recovers mu(k)/k from
prime-power exponent data. Perfect-power dilation and formal LOG give
the exact prime indicator at EVERY integer, with a generic universal
inverse. Complete coefficient checks through 4096, held-out exponent
identities through 64 and unrelated rational inputs verify the code.
This is classical calibration, not a new prime-distribution estimate.
The derivative-weighted logarithm separately gives Lambda; actual-prime
counts and prime-power mass are distinguished and stripped explicitly.

The floor grammar scores 78,125 integer coefficient vectors. There are
543 balanced primitive programs and 341 quarter-grid survivors. Exact
rational breakpoint certificates leave 67 kernels positive at EVERY
real scale; an independent denominator-420 grid verifies the full result.
Fifteen have height one; all 52 height-two survivors in this BOUNDED
GRAMMAR are sums of two height-one survivors. A coarse-grid alias has
w(1/7)=-2 and actual zeta trace -2*log 2 at X=2/7, rejecting extrapolation
from sampled positivity. Universal finite divisor identities give
T_c(X)=sum_a c_a*log(floor(a*X)!) for all X>=0. Exact factorials and
prime valuations agree on 180 rational-scale groups.

Mobius scale decoding recovers sum_a c_a*psi(a*X). Actual-prime mass
uses an additional prime-power removal; unweighted/residue counts use
the extracted prime indicator. At X=5 the positive central-binomial
trace is log 252, but its decoded contrast is log(7/10)<0. Positivity
and arithmetic information are therefore not preserved automatically.

Twenty complete dyadic windows cover integers through 2^20. Four
additional complete width-4096 windows start at 10^6,10^8,10^10,10^12;
their counts are 312,228,170,140. Each records residues modulo 3,5,7
and INTERNAL consecutive-prime gaps. Independent sieve/primality checks
verify every integer in the windows. These are finite observations,
not evidence of a count, gap or RH bound at every larger scale.

The Mellin symbol of every finite floor trace is
-zeta_prime(s)*A_c(s)/s: its zeta factor cancels ALL ordinary-zero poles.
Thus unmodified floor-trace holomorphy cannot be an RH test. The decoded
central contrast instead has symbol
-zeta_prime(s)/zeta(s)*(2**s-2)/s. Its scale symbol is nonzero in the
nontrivial-zero strip, so actual-zero poles return with nonzero residues.
Two old simple-zero disks certify this distinction; no new zero is found.
Subtracting the trace's linear main term also leaves an explicit
Mobius partial-sum contribution. It supplies no new critical-scale bound.

The scale decoder's generic weighted norm is exactly
zeta(sigma)/zeta(2*sigma) for sigma>1 and infinite for sigma<=1.
Exact saturating vectors and elementary squarefree-density blocks prove
the sharp boundary without RH or prime-density assumptions. This is
a GENERIC norm barrier. A new cancellation estimate on the particular
prime-derived inputs is still possible and is now a priority search target.

Six independent exact and six analytic gates pass. Six new complete
prime-weight/native-zeta groups change coefficient cutoffs 4096/6144,
complex arguments, explicit logarithm tails and wrong-prime controls.
They bring the cumulative full count to {bridge_count}. Six floor-trace
Mellin groups, squarefree norm controls and reused zero disks are auxiliary.
Mobius inversion and Landau/factorial-ratio kernels are established.
No new all-scale prime estimate, historical novelty or RH proof is claimed.
The research objective remains active. Proof: prime_scale_proof.txt;
data: prime-scale-results/; figure: prime-scale-results/prime_scale_overview.png and .pdf.

CREATIVE GRAMMAR AND EXTERNAL QRH CALIBRATION

Typed productions cover arithmetic sequences, residue vectors/maps and
prime arithmetic scalars, with explicit linear/anti-linear semantics.
Every serialized tree is checked for domain, sort, parameter and support.
The public program_value entry point executes learned kernels and the
normalized Gauss conversion. Composite and nonunit mistakes are controls.

The word search evaluates {creative['operator_word_search']['map_programs_evaluated']:,} maps at full training bases 7,13,
yielding {creative['operator_word_search']['distinct_training_fingerprints']:,} distinct fingerprints. Sound rewrites prove
{creative['operator_word_search']['universal_rewrite_certified_aliases']:,} aliases; {creative['operator_word_search']['unproved_training_aliases']:,} finite matches remain unproved after fresh-prime
probes. None is promoted to a universal theorem merely by those probes.
K=F^*INV MASK F recovers a normalized Kloosterman operator with
K^2=I-J/p, K^3=K, rank p-1 and norm one for every prime.
Its energy on complete Mobius residue embeddings is independently checked.
The identity is generic projection algebra, with no new mu cancellation
or ordinary-zeta zero-fidelity theorem after the embedding.

The sampled Fourier/inversion commutator rank has now been proved:
rank[F,INV]=p-3 for every odd prime. Multiplicative characters diagonalize
the nonzero residue block. Classical cyclotomic independence excludes
zero eigenvalues except at the trivial and quadratic characters; row zero
supplies the third kernel direction. Native character eigenvalues provide
changed-arithmetic controls. No uniform nonzero singular-value lower bound
or new ordinary-zeta/prime-distribution consequence is proved.

Sixteen phase-product programs have exact graded associator laws. In the
case w(x,y)=e_p(x*y^2), the associator is e_p(-2*x*y*z). Replacing grades
by Omega gives an all-integer Dirichlet lift, initially Re(s)>1. An unknown
ten-coefficient polynomial kernel search recovers four universal cocycles;
all execute through the public grammar. Six characteristic-three fits fail
at another prime. Vocabulary, degree and word depth still bias the search.

The QRH source snapshot is {qrh['source_commit']['sha']}.
Its Gauss conversion is recovered among 432 programs; 816 finite Fourier
identities pass exact cyclotomic and independent native-complex audits.
Cube inversion, whole-index masks and fixed-slot scale compensation have
universal algebraic controls. The local rational replacement test is a
principal-row integer proxy; full theta reflection and global Hecke-family
moment bounds remain unimplemented. This does not independently certify
either full QRH proof. Six QRH and six creative audit gates pass.
These external/finite-space calibrations do not change the ten ordinary
zeta families, twenty main consequences or {bridge_count} full native-zeta comparisons.
Proof: creative_grammar_proof.txt. Review: qrh_operator_review.txt.
Data: creative-results/, qrh-results/.

GLOBAL MOMENT INEQUALITIES WITHOUT A QRH-SPECIFIC TRAINING TARGET

The detector now constructs even moments, mixed energies, unknown scale
transfers and positive functionals. Every bound must state its coefficient
family, row/scale parameters, support assumptions, initial cost and
quantifiers. Its current certificate backends are orthogonality, residue
bucket Cauchy, polynomial root counting, Laurent support separation,
positive recurrence functionals, induction and geometric scale tails.

Additive twists of the complete zeta-inverse prefix supply six arithmetic
energy groups with changed scales, row moduli and polynomial index degrees.
Their generic second-moment certificate covers every integer D,H>=1:
M2<=H*ceil(D/H)*sum|a|^2. Nonlinear n^d indices have a separate
prime-field certificate; extending it to a composite modulus is rejected
by energy 256 versus the invalid bound 128 at modulus sixteen.
These are genuine all-scale generic laws, with no new mu cancellation.

The operator search scores 48 signed matrix/phase-shift programs, learning
two different fourth-moment transfers from generic inputs. There are
24 universal transfers and 16 fitted recurrences rejected on changed
coefficient spans. Exact Laurent identities and frequency support, rather
than the fit, establish the valid recurrences. Positive functional search
learns growth rates four and six, with different metric weights.

For the signed recursive family it recovers
integral|P_j|^4=(4*4^j-(-2)^j)/3 <= 3/2*N^2, N=2^j, for EVERY level.
For the lacunary positive family it recovers integral|P_j|^4=6^j.
These established polynomial families are separate calibrations; their
bounds cannot be applied to mu or primes without a certified transfer.
The source does not use QRH-specific exponents, characters or theta
objects as training targets. Scale ratios, generic inputs, operator
classes and modulus domains are distinct holdout dimensions.

Persistent forcing requires a strictly contractive normalized recurrence.
At the critical rate its accumulated cost grows with the number of
levels, hence logarithmically with scale. A constant fit through level 31
fails at 257. Homogeneous critical-rate bounds remain a separate case.
Independent Laurent expansion, binary/ternary coefficient reconstruction,
autocorrelations and native 384-bit circle integration pass all seven gates.
The target-transfer layer learns the moment/row-count exponents 1/2,-1/2
and proves |T|<=E+(B/m)^(1/q) when m rows approximate T within E and
the q-moment is at most B. Rational upper-root rounding and native complex
q=2,4,6 controls are checked. The family moment, actual arithmetic/prime
row count and error need separate uniform certificates. A smooth Mobius
target has Mellin transform hatW(s)/zeta(s), so ordinary-zero exclusion
also requires a suitable nonvanishing transform numerator. No global B,m,E
package for such a target is presently certified; finite row replication
or a bound from another coefficient family is insufficient.
No new prime-information estimate, ordinary-zeta zero bridge or QRH/RH
proof is established. The research goal stays active.
Proof: global_moment_proof.txt. Data: global-moment-results/.

FRACTIONAL PRIME DECODER AND ITS ACTUAL-ZERO ANALYTIC CERTIFICATE

A separate verified arithmetic lead is B_alpha=W[(f_D^-1*D_alpha f)(n)/
(log n)^alpha], with a universal triangular inverse. Its public grammar
executes changed real and complex units and rejects uncertain input
normalizations, nonfinite coefficients and invalid orders. On zeta,
B_alpha(p)=1 at every prime and every composite has magnitude at most
2^(1-alpha)-1<1. A universally proved strict sign law uses omega(n) and
omega(gcd prime exponents). The gap is sharp, and alpha tending to one
recovers the prime indicator in coefficient infinity norm.

Seven coefficient/API and six independent analytic gates pass. Six new
complete native comparisons evaluate L_(1/2)=N_(1/2)/zeta, not the whole
normalized B_(1/2). These are separately counted component comparisons,
outside the main {bridge_count} groups. Independent derivative integration,
whole-disk bounds, exactly tiled corridors and larger Rouché connection
disks prove a nonzero inverse-square-root branch at both old simple zeta
zeros near 14.134725i and 21.022040i. No new ordinary zero is located.
Global numerator nonvanishing, a prime-distribution estimate and RH remain
unproved. Fractional zeta differentiation is established prior art; the
closest 2024 logarithmic-fractional paper still needs a full formula
comparison. The historical-new list stays empty.
Proof: fractional_prime_proof.txt. Priority audit: fractional_prior_art_audit.txt.
Data: fractional-prime-results/.

MOMENT-TO-PRIME-COUNT TARGETS ON THE ACTUAL ARITHMETIC FAMILY

Generic saturation cases learn twelve affine support/moment transfers,
with universal endpoint certificates and changed complex/weighted controls.
If marked scores have modulus one, other scores have modulus <=delta<1,
and weights sum to W, a certified coefficient moment enclosure gives
max(0,(M_lo-delta^(2k)*W)/(1-delta^(2k))) <= count <= min(W,M_hi).
The order compiler retains scale dependence and certifies integer recovery
only when the count interval has width below one. This applies to actual
primes using the decoder's all-integer gap, without prime labels as moment
inputs. Sixteen finite arithmetic groups give eight unique integer counts:
the tenth coefficient moment recovers 564 primes through 4096, and tested
residues modulo three and seven recover 277 and 97.

Complete Fourier second moments of the coefficientwise-power family equal
H*M_(2k) when support residues are distinct modulo H. Six changed native
groups include composite moduli. Modular aliasing and substituting ordinary
circle fourth moments for coefficient fourth moments are rejected.

The new least-prime-factor envelope |B_alpha(n)| <=
(log P^-(n)/log n)^alpha has a universal proof and a sharp exponent.
Sixteen exponent models include a false 11/20 roughness exponent for
B_(1/2) that passes all indices through 4096 but fails at n=2*q near
2*10^12, with q an actual prime. Using the cited uniform rough-number
theorem and layer-cake
integration gives a genuine all-scale upper bound: for gamma=2*k*alpha>1,
M_(2k)([X,2X]) <= 2*gamma/(gamma-1)*X/log X, every integer X>=2.
In particular, M4 for B_(1/2) is at most 4*X/log X. Injective Fourier
families therefore have second moment <=4*H*X/log X. The critical envelope
retains a loglog scale cost; this does not rule out a better actual M2
bound using more arithmetic structure. Seventy-two changed moment groups,
twenty native truncated integrals and six independent audit gates pass.
This upper bound imports known prime-distribution information; it supplies
no new independent prime estimate. The imported sieve proof itself was
not independently reverified in full. Ordinary-zero sensitivity of the
original decoder does not automatically transfer to its coefficientwise
powers. This calibration is recorded
separately from the ten main families, twenty consequences and main
native-zeta comparisons. No new prime distribution or RH estimate is proved.
Proofs: prime_moment_transfer_proof.txt and prime_roughness_moment_proof.txt.
Data: prime-moment-results/.

UNEQUAL-SHIFT PRIME DECODERS WITH AN UNCONDITIONAL LOCAL ZERO SIGNATURE

The expanded grammar executes R_v(f)(n)=sum_(ab=n,b>1)
f_Dinv(a)*f(b)*log(b)/(log(b)+v*log(a)), B_v=W R_v, and its universal
triangular inverse. No prime labels enter its coefficient production.
For 0<v<1, B_v(p)=1, composite modulus <=(1-v)/(1+v) with a sharp
gap, and the strict sign is (-1)^(omega(n)+omega(gcd prime exponents)-1).
Its least-prime envelope is t/(v+(1-v)*g*t), t=log P^-(n)/log n.
Arbitrary finite positive rational mixtures are also executable; their
averaged kernels have the same triangular inverse and a positive zero
signature at every multiplicity. Three held-out mixtures are independently
checked. The known rough-number theorem supplies an all-scale SECOND moment
<=2*(1+v)/v * X/log X. This imports sieve information rather than proving
a new prime-distribution estimate. The earlier fractional family is a
Beta(alpha,1-alpha) positive mixture of these unequal-shift operators;
averaging this M2 constant fails for that beta law's infinite inverse moment.

Seven independent arithmetic/API and six independent analytic gates pass.
All 16,380 coefficients, 28 doubling moments, native beta identities and
changed real/complex inverses are checked. Six complete native comparisons
evaluate B_v itself via -integral zeta'(s+t)/zeta(s+v*t)dt followed by
the full Mobius scale sum, with both infinite tails. The independent
checker changes variables, precision, meshes, cutoffs and wrong-prime controls.
It checkpoints each native group with source, checker and precision hashes.
These six are separate from the main {bridge_count} native comparison groups.

A zero of order m has nonzero local logarithmic coefficient m/v^m.
This requires a rightward zero-free corridor but no unknown fractional
numerator. Twenty native toy zero-order controls learn the multiplicity law;
independent CAS residues and changed contour toys check it. Both old actual
simple-zero disks have fresh whole-disk coefficient and nested Rouche checks,
backed by the already audited horizontal corridors. No new zero is located.

For any fixed 0<v<1, subtracting the known pole contribution yields
T_v(s)=B_v(s)+v*(1/zeta)'(v+(1-v)*s)*log(s-1). Single-valued holomorphic
continuation of this function to Re(s)>1/2 is equivalent to RH. The
converse uses a finite-height extremal zero, avoiding an assumed globally
rightmost zero. Neither this equivalence nor the coefficient energy bound
proves the continuation. Historical priority of the compound construction
is unresolved; near v=1 the family is a verified geometric combination of
known integer arithmetic logarithms, so no new primitive is claimed. The
verified-historically-new list remains empty.
Proof: shift_ratio_proof.txt. Priority: shift_ratio_prior_art_audit.txt.
Data: shift-ratio-results/.
Figure: shift-ratio-results/shift_ratio_overview.png and .pdf.
To resume a stopped independent analytic audit, rerun
../.venv/bin/python check_shift_ratio_analytic.py with its source retained.
Its --native-group j option verifies a single group before the full audit.

ESTIMATES ARE NOW FIRST-CLASS SEARCH TARGETS

The estimate stage generates twenty smoothing kernels before inspecting the
arithmetic input. Its Dirichlet inversion uses no prime oracle. Seven growth
exponents and five logarithmic costs generate 700 bounds, trained through
1024 and checked at fifteen held-out scales through 131072. Independent
factorizations recompute every inverse coefficient and all 560 observations.
The post-fit Mellin/known-zero gate rejects 340 impossible global estimates,
including 214 that survived every finite test. For W=(1-u)^4, an apparent
constant bound survives all held-out scales but its nonzero zeta-zero residue
rules out the all-scale claim. A numerical fit remains distinct from a proof.

The search learns prime-dilation cancellation rows and synthesizes the
classical bound |M(X)|<=X/4+3/4 from their exact boundary counts. It also
constructs twelve all-scale positive moment bounds by differentiating and
integrating the declared least-prime envelopes with the cited classical
rough-number theorem. Two mixture constants strictly improve the previous
Jensen bounds; one drops from 6.0476190476 to 5.7297032513. These are classical
theorem consequences, not newly established prime-distribution estimates.
Exact antiderivatives, changed-variable native integrals and complete actual
arithmetic moment controls pass six independent audit gates. Better signed
cancellation bounds retain explicit missing-proof obligations. No RH-level
cancellation estimate or historically new operator is established.
Proof: estimate_proof.txt. Data and figures: estimate-results/.

ESTIMATE OBLIGATIONS FEED BACK INTO THE OPERATOR SEARCH

The feedback grammar composes learned prime-dilation rows into the exact
identity S_W(X)=sum_(gcd(n,P)=1)mu(n)*sum_(d|P)mu(d)*W(d*n/X).
It preserves the original target and its ordinary-zeta Mellin transform.
Four learned primes and fourteen conditioning sets generate 280 certified
affine estimates from positive piecewise Bernstein envelopes and elementary
finite-sieve discrepancy. No external prime-distribution theorem is used
in this feedback layer. The calibration W=1-u,P=2 gives X/8+1 for every scale.
All parameter-dependent boundary costs are retained.

The engine then attempts the original 360 unresolved growth estimates.
It combines a monotone tail inequality with exact checks of every initial
integer scale, and records small-scale counterexamples where appropriate.
It also synthesizes revised constants and certifies
{estimate_feedback['repaired_all_scale_estimates_proved']} repaired all-scale estimates. These prove linear or weaker growth;
no square-root cancellation, new independent prime estimate or RH bound
is proved. Five independent feedback gates replay every polynomial envelope,
arithmetic partition, initial-scale proof and monotone tail certificate.
Proof: cancellation_rewrite_proof.txt. Evidence: estimate-results/.

Registry: candidate_registry.json. Publication-history audit: ../novelty_audit.txt.
Data: root-results/, shift-results/, transfer-results/, global-results/,
dyadic-results/, projection-results/, coupling-results/, size-results/,
joint-results/, cancellation-results/, mixed-index-results/, difference-results/,
pair-results/, decode-results/, prime-pair-results/, visible-results/, gap-results/,
laplacian-results/, moment-results/, radix-results/, prime-scale-results/,
creative-results/, qrh-results/, global-moment-results/, fractional-prime-results/,
prime-moment-results/, shift-ratio-results/, estimate-results/.
Proofs: root_proofs.txt, mixed_root_proofs.txt, carry_zero_proof.txt,
schur_root_proof.txt, shift_operator_proofs.txt, root_transfer_proof.txt,
global_carry_proof.txt, dyadic_root_proof.txt, projection_proof.txt,
coupling_proof.txt, size_carry_proof.txt, size_resonance_proof.txt,
joint_size_proof.txt, cancellation_proof.txt, mixed_index_proof.txt,
difference_proof.txt, pair_proof.txt, decode_proof.txt, prime_pair_proof.txt,
visible_proof.txt, gap_proof.txt, laplacian_proof.txt, moment_proof.txt,
radix_proof.txt, prime_scale_proof.txt, creative_grammar_proof.txt,
global_moment_proof.txt, fractional_prime_proof.txt, prime_moment_transfer_proof.txt,
prime_roughness_moment_proof.txt, shift_ratio_proof.txt, estimate_proof.txt,
cancellation_rewrite_proof.txt in the
project directory.
Run: ../.venv/bin/python run_expanded_probe.py (from this project directory).
Creative/moment stages only: ../.venv/bin/python run_expanded_probe.py --creative-only.
Fractional/arithmetic-moment stages only: ../.venv/bin/python run_expanded_probe.py --fractional-only.
Moment stages with analytic artifacts retained: ../.venv/bin/python run_expanded_probe.py --prime-moments-only.
Unequal-shift stages only: ../.venv/bin/python run_expanded_probe.py --shift-ratio-only.
Estimate certificate search only: ../.venv/bin/python run_expanded_probe.py --estimates-only.
The discovery stages reuse existing zeta observations. The analytic stages
independently evaluate actual zeta at fresh complex arguments.
"""
    report += "\nFROZEN INDEPENDENT SEARCH STAGE\n\n"
    if autonomous["status"] == "not_run":
        report += "Not yet published. Run --autonomous-only for a fresh bounded pilot.\n"
    else:
        report += (f"Frozen protocol: {autonomous['protocol_sha256']}\n"
                   f"Baseline programs: {autonomous['counts']['baseline']['generated_programs']}. "
                   f"Automatic baseline promotions: {autonomous['counts']['baseline']['automatic_promotions']}.\n"
                   f"Named anonymous calibration: {autonomous['named_calibration']}. "
                   f"Independent randomized in-language targets: {autonomous['independently_sampled_synthetic']}.\n"
                   f"Independent checks: {sum(autonomous['checks'].values())}/{len(autonomous['checks'])}. "
                   f"Accepted false controls: {autonomous['false_controls_accepted']}.\n"
                   "Final cases are created after selection is sealed; worker access to private/final "
                   "files, network and process launches is denied. Numerical leads survive missing "
                   "certificate methods. Promotion-disabled ablation receives the same generation attempts.\n"
                   "These finite results add no new all-scale prime estimate, ordinary-zeta zero bridge "
                   "or historical novelty. Main arithmetic and native-zeta counts are unchanged.\n"
                   f"Detailed report: {autonomous['run_directory']}/report.txt.\n")
    report += "Run a fresh pilot: ../.venv/bin/python run_expanded_probe.py --autonomous-only.\n"
    report += "\nPRIMARY SIGNED ARITHMETIC CONTROL SEARCH\n\n"
    if signed_control["status"] == "not_run":
        report += "Not yet published. Run --signed-control-only for a fresh sealed search.\n"
    else:
        report += (f"Generated operators: {signed_control['programs_generated']}; "
                   f"archived: {signed_control['operators_archived']}. "
                   f"Independent checks: {sum(signed_control['checks'].values())}/{len(signed_control['checks'])}.\n"
                   f"Exact final-window moment values: {signed_control['independent_complete_moment_values']}. "
                   f"Finite estimates passed: {signed_control['complete_final_estimates_passing_finite_windows']}/"
                   f"{signed_control['complete_final_estimates']}.\n"
                   "The signed sum is formed before taking moments. Every archived scale operator has "
                   "a certified all-height ordinary-zeta multiplier and explicit inverse cost.\n"
                   "Uniform moment premises remain missing. A finite fit or finite list of moment orders "
                   "does not establish the limiting exponent needed for RH. Historical novelty is not a gate.\n"
                   f"Detailed report: {signed_control['run_directory']}/report.txt.\n")
    report += "Fresh signed-control search: ../.venv/bin/python run_expanded_probe.py --signed-control-only.\n"
    report += "\nSIGNED SCALE POLYNOMIALS BEYOND TRIANGLE CONTRACTION\n\n"
    if stable_scale["status"] == "not_run":
        report += "Not yet published. Run --stable-scale-only for a fresh sealed search.\n"
    else:
        report += (f"Generated programs: {stable_scale['generated']}; all-height certified: "
                   f"{stable_scale['all_height_certified']}; certified outside the triangle domain: "
                   f"{stable_scale['certified_outside_triangle_domain']}.\n"
                   f"Unsupported programs retained: {stable_scale['retained_without_available_global_certificate']}. "
                   f"Independent checks: {sum(stable_scale['checks'].values())}/{len(stable_scale['checks'])}.\n"
                   f"Complete final moments: {stable_scale['exact_complete_moment_values']}; "
                   f"finite estimates passed: {stable_scale['finite_estimates_passed']}/{stable_scale['finite_estimates_total']}.\n"
                   "Coefficients are not projected into a triangle-contraction domain. Exact rational "
                   "disk certificates and a reciprocal prefix plus Cauchy tail supply all-height "
                   "root preservation and inverse bounds. Ranking includes the full recovery cost.\n"
                   "These are operator properties. The sublinear all-scale moment premises remain unproved, "
                   "and no RH proof follows from this finite pilot.\n"
                   f"Detailed report: {stable_scale['run_directory']}/report.txt.\n")
    report += "Fresh scale-polynomial search: ../.venv/bin/python run_expanded_probe.py --stable-scale-only.\n"
    report += "\nDIRECT SIGNED MOMENT CONTROL: PRIMARY RH PROOF TARGET\n\n"
    report += ("Holder's inequality gives the direct Mellin exponent eta=(beta-1)/q. "
               "A single fixed moment order can suffice for RH: an independently proved "
               "all-scale beta=q/2+1 bound with an all-height nonzero ordinary-zeta multiplier "
               "excludes every zero right of 1/2. The earlier finite-order warning was too broad; "
               "a limiting family is one route, not a mandatory form of a proof.\n")
    if signed_mellin["status"] != "not_run":
        report += (f"Additional universal audit of earlier pilots: {signed_mellin['programs_audited']} programs "
                   f"and {signed_mellin['estimates_audited']} moment estimates; "
                   f"{sum(signed_mellin['checks'].values())}/{len(signed_mellin['checks'])} independent checks. "
                   f"{signed_mellin['finite_passes_globally_ruled_out']} finite-window passes are "
                   "nevertheless ruled out as uniform estimates by an actual ordinary zeta zero. "
                   "This later audit neither reselects candidates nor makes a new held-out claim.\n")
    if mellin_search["status"] == "not_run":
        report += "Primary direct-Mellin search has not yet been published.\n"
    else:
        report += (f"Primary search: {mellin_search['generated']} generated programs, "
                   f"{mellin_search['archived']} archived; "
                   f"{sum(mellin_search['checks'].values())}/{len(mellin_search['checks'])} independent checks. "
                   f"{mellin_search['exact_complete_moment_values']} exact complete final moments.\n"
                   f"Viable obligations passing fresh windows: {mellin_search['viable_obligations_passing_fresh_windows']}; "
                   f"RH-sufficient obligations among them: {mellin_search['RH_sufficient_obligations_passing_fresh_windows']}. "
                   "Their uniform arithmetic premises remain unproved; RH is unproved.\n"
                   f"Detailed report: {mellin_search['run_directory']}/report.txt.\n")
    report += "Fresh primary search: ../.venv/bin/python run_expanded_probe.py --mellin-only.\n"
    if signed_defects["status"] != "not_run":
        report += ("\nLEARNED SIGNED MOMENT RECURRENCES\n\n"
                   f"Inferred recurrences: {signed_defects['recurrences_generated']}; "
                   f"archived: {signed_defects['archived']}; "
                   f"independent checks: {sum(signed_defects['checks'].values())}/{len(signed_defects['checks'])}. "
                   f"Exact actual moment values checked: {signed_defects['exact_actual_moment_values_checked']}.\n"
                   f"RH-sufficient recurrences passing fresh windows: {signed_defects['RH_sufficient_recurrences_passing_fresh_windows']}. "
                   "The original Mobius sum is a baseline; filters have no demonstrated advantage under this criterion. "
                   "The uniform signed recurrence premises remain unproved.\n"
                   f"Detailed report: {signed_defects['run_directory']}/report.txt. "
                   "Fresh run: --signed-defects-only.\n")
    if fractional_moments["status"] != "not_run":
        report += ("\nRATIONAL ROOTS AND FRACTIONAL SIGNED MOMENTS\n\n"
                   "The grammar accepts exact rational exponents, signed real powers, ordinary real powers, "
                   "absolute powers, declared principal complex branches and normalized Dirichlet powers. "
                   "Its semantics have no fixed denominator ceiling.\n"
                   f"Effective orders: {fractional_moments['effective_orders']}. "
                   f"Inferred estimates: {fractional_moments['estimates_generated']}; archived: {fractional_moments['archived']}; "
                   f"independent checks: {sum(fractional_moments['checks'].values())}/{len(fractional_moments['checks'])}.\n"
                   f"Certified complete moment values checked: {fractional_moments['certified_actual_moment_values_checked']}; "
                   f"exact Dirichlet coefficients: {fractional_moments['exact_Dirichlet_coefficients_checked']}; "
                   f"native zeta root checks with proved tails: {fractional_moments['native_zeta_root_checks']}.\n"
                   "Root amplitudes are audited through their inverse and effective moment order. "
                   "Holder is used at orders >=1; lower orders have an explicit Lipschitz loss. "
                   "Whole-window fractional moments are certified algebraic enclosures, not exact rational values.\n"
                   f"RH-sufficient obligations passing fresh windows: {fractional_moments['RH_sufficient_obligations_passing_fresh_windows']}. "
                   "Their uniform signed arithmetic premises remain unproved. RH remains unproved.\n"
                   f"Proof: rational_power_proof.txt. Detailed report: {fractional_moments['run_directory']}/report.txt. "
                   "Fresh run: --fractional-powers-only --max-root-denominator 12.\n")
    if fractional_branches["status"] != "not_run":
        report += ("\nLOCAL FRACTIONAL-ZETA BRANCH OBSTRUCTIONS\n\n"
                   f"Independent checks: {sum(fractional_branches['checks'].values())}/{len(fractional_branches['checks'])}; "
                   f"rational exponents audited: {fractional_branches['rational_exponents_audited']}; "
                   f"fractional pole branches detected: {fractional_branches['fractional_pole_branches_detected']}. "
                   "Different native contours certify one pole and zero zeros near s=1.\n"
                   "Every noninteger zeta power retains an uncompensated branch at one. "
                   "An integer-order analytic multiplier outside the power cannot remove it. "
                   "Joint pole compensation before taking a root fixes the local divisor only. "
                   "Negative powers retain every zero multiplicity; positive roots need a separate all-multiplicity zero bridge.\n"
                   "This is a guided analytic calibration, separate from the fresh arithmetic search and the core native counts. "
                   "It establishes no uniform signed moment bound or RH proof.\n"
                   f"Proof: fractional_zeta_branch_proof.txt. Report: {fractional_branches['run_directory']}/report.txt.\n")
    if signed_global["status"] != "not_run":
        report += ("\nNAMED IMPORTED ALL-SCALE SIGNED CALIBRATION\n\n"
                   f"Independent checks: {sum(signed_global['checks'].values())}/{len(signed_global['checks'])}; "
                   f"complete finite patch through {signed_global['independent_complete_coefficient_cutoff']}. "
                   f"Inferred C={signed_global['constant']}: {signed_global['uniform_bound']}.\n"
                   "The infinite range relies on Ramare and Zuniga Alterman, arXiv:2408.05969v2, Theorem 1.1. "
                   "That external analytic argument and its imported prime estimates have not been independently re-proved. "
                   "Signed dilation costs transfer this logarithmic control to the eight source residuals. "
                   "These imported consequences supply signed o(t) calibration, below RH strength.\n"
                   f"Proof: signed_global_calibration_proof.txt. Report: {signed_global['run_directory']}/report.txt.\n")
    if pole_neutral["status"] != "not_run":
        report += ("\nSIGNED FRACTIONAL COEFFICIENTS AND LOGARITHMIC KERNELS\n\n"
                   "The grammar independently varies nu_a=mu^a, a fractional integral order b, and a real shift kappa. "
                   "Their exact Mellin transform is zeta(s)^(-a)*(s-kappa)^(-b)/s. Local divisor audits "
                   "find compatible pole compensation and reject branch obstructions. Negative powers retain every ordinary zero multiplicity.\n"
                   f"Programs: {pole_neutral['programs']}; estimates: {pole_neutral['estimates']}; archived: {pole_neutral['archived']}; "
                   f"independent checks: {sum(pole_neutral['checks'].values())}/{len(pole_neutral['checks'])}. "
                   f"Complete signed point values checked: {pole_neutral['complete_signed_values_checked']}; "
                   f"exact coefficients: {pole_neutral['exact_coefficients_checked']}.\n"
                   f"RH-sufficient obligations passing fresh points: {pole_neutral['RH_sufficient_obligations_passing_fresh_points']}; "
                   f"finite passes nevertheless globally contradicted: {pole_neutral['finite_passes_nevertheless_globally_contradicted']}. "
                   "The integer-to-real extension and full inverse-power height costs are retained. "
                   "These are complete point sums, not complete window moments. Their uniform signed arithmetic premises remain unproved.\n"
                   f"Proof: pole_neutral_proof.txt. Report: {pole_neutral['run_directory']}/report.txt.\n")
    if parameter_jets["status"] != "not_run":
        report += ("\nGENERAL PARAMETER JETS AND ACTUAL-PRIME ERROR\n\n"
                   "The general grammar computes arbitrary-order coefficient-power jets at any rational centre. "
                   "Coefficient and kernel slopes vary independently. The matched first jet is "
                   "lim_(a->0+) (G_a(x)-1)/a = li(x)-sum_(p^k<x)1/k for every fixed real x>1. "
                   "Exact root-count inversion recovers ordinary strict prime counts without a producer prime oracle.\n"
                   f"Independent checks: {sum(parameter_jets['checks'].values())}/{len(parameter_jets['checks'])}; "
                   f"exact coefficient values: {parameter_jets['exact_coefficient_values_checked']}; "
                   f"rigorous Cauchy kernel coefficients: {parameter_jets['rigorous_Cauchy_kernel_coefficients']}. "
                   f"Complete family jet values: {parameter_jets['complete_family_jet_values_checked']}.\n"
                   "A bound proportional to a*sqrt(x), allowing fixed logarithmic losses, uniform for x>=2 "
                   "and every sufficiently small positive a would imply RH. That coupled signed bound remains unproved. "
                   "This is guided identity recovery, not autonomous discovery of a prime estimate; the analytic argument "
                   "is mathematical prose and is not machine-formalized.\n"
                   f"Proof: parameter_jet_proof.txt. Report: {parameter_jets['run_directory']}/report.txt.\n")
    if prime_error["status"] != "not_run":
        report += ("\nSIGNED PRIME-ERROR FILTERS WITHOUT A NONVANISHING GATE\n\n"
                   "The observable is li(x)-sum_(p^k<x)1/k, truncated below two. Signed finite dilations "
                   "give a non-identically-zero entire multiplier. It may have isolated zeros inside the critical half-plane. "
                   "The derivative of a meromorphic quotient has zero residue, while zeta'/zeta has residue equal "
                   "to every positive ordinary zero multiplicity. Thus isolated multiplier zeros cannot erase "
                   "the logarithmic zero information. This conditional bridge requires no all-height nonvanishing certificate.\n"
                   f"Independent checks: {sum(prime_error['checks'].values())}/{len(prime_error['checks'])}; "
                   f"programs: {prime_error['programs']}; estimates: {prime_error['estimates']}; archived: {prime_error['archived']}. "
                   f"Complete signed point values: {prime_error['complete_signed_point_values_checked']}; "
                   f"exact coefficients: {prime_error['exact_coefficients_checked']}; final prefix: {prime_error['complete_coefficient_cutoff']}.\n"
                   f"Fresh RH-sufficient-if-uniform survivors: {prime_error['RH_sufficient_obligations_passing_fresh_points']}; "
                   f"surviving filters with multiplier zero at one: {prime_error['surviving_filters_failing_old_gate_by_zero_at_one']}; "
                   f"finite survivors nevertheless globally ruled out: {prime_error['finite_passes_nevertheless_globally_ruled_out']}.\n"
                   "Whole-unit prime-power jumps have a scale-independent bound, extending uniform integer estimates "
                   "to every real scale without changing theta. Costs charge exponential logarithmic reconstruction "
                   "at a fixed point; no all-height quantitative quotient bound is claimed. The actual-zero native "
                   "calibration uses rigorously bounded Taylor remainders and is separately guided. "
                   "All RH-strength signed arithmetic premises remain unproved.\n"
                   f"Proof: prime_error_proof.txt. Report: {prime_error['run_directory']}/report.txt.\n")
    if prime_discrepancy["status"] != "not_run":
        density=prime_discrepancy["selected_prime_density_certificate"]
        report += ("\nALL-SCALE PRIME INPUTS AND SIGNED PRIME-ERROR CORRELATIONS\n\n"
                   "The floor grammar automatically certifies exact zero drift and nonnegative cells over a full period. "
                   "A factorial trace and an elementary dyadic tail prove actual-prime density at every real scale. "
                   f"Carry proposals: {prime_discrepancy['carry_proposals']}; universal certificates: {prime_discrepancy['universal_floor_certificates']}. "
                   f"Selected coefficients: {density['coefficients']}; psi(x)<={density['density']['constant']}*x for every x>=1. "
                   "No prime-distribution estimate is imported in this stage.\n"
                   "Prime-error increments give A2=D+C_off on complete windows. The all-scale diagonal bound "
                   "D<=3*C_a*S^2*X^2/log(e+X) is unsigned. C_off keeps the missing signed pair information. "
                   "Regression and generic rational grids propose C_off<=rho*D+B*X^gamma. "
                   "For matched prime error, rho>-1 and gamma<=2 would suffice for RH if uniform; the "
                   "logarithmic residue bridge permits isolated multiplier zeros.\n"
                   f"Independent checks: {sum(prime_discrepancy['checks'].values())}/{len(prime_discrepancy['checks'])}; "
                   f"programs: {prime_discrepancy['programs']}; estimates: {prime_discrepancy['estimates']}; archived: {prime_discrepancy['archived']}. "
                   f"Complete actual windows: {prime_discrepancy['complete_actual_windows_checked']}; "
                   f"support-control windows: {prime_discrepancy['complete_support_control_windows_checked']}; "
                   f"final prefix: {prime_discrepancy['complete_coefficient_cutoff']}.\n"
                   f"Fresh RH-sufficient-if-uniform survivors: {prime_discrepancy['RH_sufficient_obligations_passing_fresh_windows']}; "
                   f"finite survivors nevertheless globally ruled out: {prime_discrepancy['finite_passes_nevertheless_globally_ruled_out']}. "
                   "All uniform signed pair premises remain open; the proved prime and diagonal inputs are recorded separately.\n"
                   f"Proof: prime_discrepancy_proof.txt. Report: {prime_discrepancy['run_directory']}/report.txt.\n")
    if prime_twists["status"] != "not_run":
        report += ("\nFRACTIONAL PRIME TWISTS AND SIGNED DECAY\n\n"
                   "The factorial trace now supplies signed information about actual primes at every scale: "
                   f"-1<=sum_(p^k<x)log(p)/p^k-log x<={prime_twists['prime_density_constant']} for every real x>=2. "
                   "Partial summation proves "
                   f"|sum_(p^k<x)1/(k*p^k)-log(log x)-gamma|<={prime_twists['mertens_logarithmic_constant']}/log x. "
                   "A corresponding centered tail bound holds for every real fractional order nu>=1. "
                   "These supplied arithmetic proof backends are below RH strength: ordinary-zeta recovery costs the leading shift, "
                   "leaving exponent one. No imported prime-distribution estimate or autonomous proof invention is claimed.\n"
                   "The expanded grammar has lambda and Lambda channels, independent normalizers, negative rational growth exponents, "
                   "and exact Mellin centers. A finite right-shift multiplicity chain recovers every ordinary zero, including "
                   "local shifted-zero coincidences. Quantitative recovery charges every path and Euler endpoint.\n"
                   f"Independent checks: {sum(prime_twists['checks'].values())}/{len(prime_twists['checks'])}; "
                   f"programs: {prime_twists['programs']}; estimates: {prime_twists['estimates']}; archived: {prime_twists['archived']}. "
                   f"Complete coefficient prefix: {prime_twists['complete_coefficient_cutoff']}; "
                   f"unrelated signed response values: {prime_twists['generic_signed_response_values_checked']}.\n"
                   f"Original gate RH-sufficient-if-uniform finite survivors: {prime_twists['RH_sufficient_obligations_passing_fresh_points']}; "
                   f"negative-decay survivors: {prime_twists['negative_decay_RH_sufficient_obligations_passing_fresh_points']}; "
                   f"finite passes rejected by the original pole/isolated-zero gates: {prime_twists['finite_passes_nevertheless_globally_ruled_out']}. "
                   "The later oscillation audit supersedes these plausibility counts.\n"
                   "Delayed attenuated controls preserve actual prime-power locations and the same global density and diagonal bounds. "
                   "Their 1/k weights change above 8192. Native shifted poles independently rule out uniform RH estimates. "
                   f"Whole fresh-window passes by those false controls: {prime_twists['finite_density_matched_control_bound_passes']}. "
                   "All RH-strength signed decay and pair premises remain unproved.\n"
                   f"Proof: prime_twist_proof.txt. Report: {prime_twists['run_directory']}/report.txt.\n")
    if prime_twist_coverage["status"] != "not_run":
        report += ("\nEXHAUSTIVE FINITE PRIME-TWIST COVERAGE\n\n"
                   f"Every integer through {prime_twist_coverage['cutoff']} was checked for all frozen archived estimates: "
                   f"{prime_twist_coverage['complete_point_comparisons']} native interval point comparisons. "
                   f"Every complete window start through {prime_twist_coverage['complete_window_starts']} was checked for the three unfiltered pair bounds: "
                   f"{prime_twist_coverage['complete_moment_comparisons']} moment comparisons. "
                   "No source formula or fitted constant was changed. This evaluator extension retains cumulative-prefix overlap with development data. "
                   "Finite success remains an unproved universal premise and is subject to the later analytic gate.\n"
                   f"Report: {prime_twist_coverage['run_directory']}/report.txt.\n")
    if prime_oscillation["status"] != "not_run":
        report += ("\nOSCILLATION COMPATIBILITY AND POSITIVE-LOG REPAIR\n\n"
                   "The named Hardy-Littlewood oscillation theorem rules out psi(x)-x=O(sqrt(x)). "
                   "An exact eventual polynomial inverse and Stieltjes integration show that every compensated pure critical-power Lambda-channel "
                   "bound in the audited class implies that forbidden estimate. Fractional twists and signed polynomials are covered. "
                   "The classical oscillation proof is an external dependency, not independently re-proved.\n"
                   f"Complete candidates checked: {prime_oscillation['complete_candidates_checked']}; generic rejection certificates: {prime_oscillation['oscillation_certificates_checked']}; "
                   f"distinct eventual-inverse programs: {prime_oscillation['distinct_eventual_inverse_programs_checked']}. "
                   f"Previously successful finite archived bounds now known false: {prime_oscillation['globally_false_original_finite_survivors']}. "
                   f"Original finite RH-compatible estimates remaining after the gate: {prime_oscillation['original_RH_compatible_survivors_after_new_gate']}.\n"
                   "Weighted lambda channels and arbitrary positive rational log powers remain eligible. An automatic selector chose repairs from the "
                   "original candidate batch using source validation and charged costs, then sealed them before new final evaluation. "
                   f"Positive-log repairs passing every fresh interval point: {prime_oscillation['positive_log_repairs_passing_fresh_interval']}; "
                   f"interval: {prime_oscillation['fresh_integer_interval']}; independently checked point values: {prime_oscillation['fresh_complete_point_values_checked']}. "
                   f"Independent checks: {sum(prime_oscillation['checks'].values())}/{len(prime_oscillation['checks'])}.\n"
                   "The original finite data are preserved. All RH-strength uniform signed premises remain unproved.\n"
                   f"Proof: prime_oscillation_proof.txt. Report: {prime_oscillation['run_directory']}/report.txt.\n")
    if fractional_remainders["status"] != "not_run":
        report += ("\nFRACTIONAL ARITHMETIC REMAINDERS WITH INFINITE-PARAMETER RECOVERY\n\n"
                   "The new primitive subtracts a continuous logarithmic integral from the cumulative fractional arithmetic logarithm. "
                   "At order zero it equals 1-x*sum_(d<=x)mu(d)/d. Its pole-subtracted Mellin numerator is entire in s. "
                   "A nonzero parameter-pole residue prevents ALL orders of a fixed compensated rational family from erasing an ordinary zeta zero. "
                   "The proof requires an infinite order schedule; finite parameter probes never establish the universal premise. "
                   "High-pass families with vanishing small-order limits are covered.\n"
                   f"Primary programs: {fractional_remainders['programs']}; growth hypotheses: {fractional_remainders['growth_hypotheses']}; "
                   f"native entire-numerator queries checked: {fractional_remainders['native_entire_numerators_checked']}; "
                   f"full Cauchy-cover subboxes: {fractional_remainders['native_reciprocal_gamma_subboxes_checked']}. "
                   f"Global signed-parameter and unit-bound certificates: {fractional_remainders['proved_global_family_and_unit_bound_certificates']}. "
                   "Those true all-scale bounds have x-growth exponent one and do not prove RH.\n"
                   f"Fresh integer scales: {fractional_remainders['fresh_integer_scales']}; fresh order parameters: {fractional_remainders['fresh_order_parameters_q']}; "
                   f"complete coefficient cutoff: {fractional_remainders['complete_coefficient_cutoff']}. "
                   f"Archived finite passes: {fractional_remainders['archived_finite_passes']}; RH-sufficient-if-uniform family leads passing: "
                   f"{fractional_remainders['RH_sufficient_family_obligations_passing_fresh_points']}. "
                   f"Known false controls passing finite probes: {fractional_remainders['known_false_controls_passing_fresh_points']}.\n"
                   "The isolated selector learns combinations and exponents, with an equal-proposal-slot promotion ablation. "
                   "Uncompensated positive-order poles and excessive parameter rates are rejected analytically. "
                   "Conditional reciprocal costs charge numerator size, parameter powers and real-scale corrections. "
                   "The proof backends are supplied and independently checked, not autonomously invented or machine formalized.\n"
                   f"Independent checks: {sum(fractional_remainders['checks'].values())}/{len(fractional_remainders['checks'])}. "
                   "All RH-strength signed uniform family estimates remain unproved. "
                   f"Proof: fractional_remainder_proof.txt. Report: {fractional_remainders['run_directory']}/report.txt.\n")
    if mertens_limits["status"] != "not_run":
        report += ("\nSMALL-ORDER INVERSE COMPATIBILITY AND LOG-LOSS REPAIRS\n\n"
                   "A common pure square-root family bound controls its exact small-order limit. "
                   "The rational Volterra/Mellin inverse charges the cost of recovering the ordinary Mertens sum. "
                   "Hurst's named published extremum theorem implies limsup |M(x)|/sqrt(x)>7/4, ruling out estimates with smaller recovered constants. "
                   "The imported large zero/phase calculation has not been independently reproduced. The limit and inverse algebra are independently checked.\n"
                   f"Complete source estimates checked: {mertens_limits['complete_candidates_checked']}; exact rejection certificates: {mertens_limits['exact_limit_rejection_certificates']}; "
                   f"original finite archived successes now ruled out: {mertens_limits['globally_false_original_finite_survivors']}. "
                   f"Original conditional RH-family survivors remaining after the gate: {mertens_limits['original_RH_compatible_survivors_after_new_gate']}. "
                   "The source's sixteen-check audit and finite results are retained; this later gate supersedes their plausibility counts.\n"
                   f"Positive-log repairs drawn from the original frozen batch: {mertens_limits['repairs_selected']}; passing fresh points: {mertens_limits['positive_log_repairs_passing_fresh_points']}. "
                   f"Fresh interval: {mertens_limits['fresh_integer_interval']}; independent complete point values: {mertens_limits['fresh_complete_point_values_checked']}. "
                   "Degree-zero repairs test every integer; positive-degree families use the declared fresh points and orders. "
                   "No repaired universal signed bound is proved.\n"
                   f"Independent checks: {sum(mertens_limits['checks'].values())}/{len(mertens_limits['checks'])}. "
                   f"Proof: mertens_limit_proof.txt. Report: {mertens_limits['run_directory']}/report.txt.\n")
    if mellin_kernels["status"] != "not_run":
        report += ("\nCOMPLETE SIGNED ARITHMETIC TAILS AND COFINAL GROWTH FRONTIERS\n\n"
                   "The supplied grammar forms signed exponential kernels with rational root scales, dilation mixtures and Euler derivatives. "
                   "Every response includes the infinite constant-one inverse tail through reciprocal-zeta moments in their absolutely convergent region. "
                   "Independent evaluation changes the factorization method, prefix, precision, Taylor order and summation algorithm.\n"
                   "Exact rational identities between the Mellin numerators certify that several kernels can recover ordinary zeta together, "
                   "even when individual scalar nonvanishing certificates are unavailable. These identities cover all heights and multiplicities. "
                   "Missing recovery certificates are retained separately from disproved estimates.\n"
                   "Growth targets have theta_q=eta+epsilon/q^nu, with a freely varying constant for each q. "
                   "Every q requires a bound over every scale. At eta=1/2 a recovering bank gives an RH-equivalent target; "
                   "no fixed square-root constant or prescribed constant growth in q is imposed. New-q constants use frozen training scales and "
                   "are sealed before fresh final scales. A finite q grid does not prove the target.\n"
                   f"Primary kernels: {mellin_kernels['program_count']}; banks: {mellin_kernels['bank_count']}; "
                   f"primary growth hypotheses: {mellin_kernels['growth_frontier_hypotheses']}. "
                   f"Joint banks with all-height recovery: {mellin_kernels['joint_banks_with_all_height_recovery']}; "
                   f"including individually uncertified kernels: {mellin_kernels['joint_banks_including_individually_uncertified_kernels']}. "
                   f"RH-if-uniform archived finite survivors: {len(mellin_kernels['RH_if_uniform_finite_survivors'])}.\n"
                   f"Counterfeit arithmetic controls passing finite tests but rejected by their uncancelled all-scale pole: "
                   f"{mellin_kernels['counterfeit_finite_successes_analytically_rejected']}. "
                   "Charged observer costs include gamma factors, all kernel members, local integrals, unit increments and the approaching-line gap.\n"
                   "Automatic global certificate attempts establish an absolute exponent-one envelope and the exact signed dilation equation. "
                   "The sublinear signed cancellation gap remains open. The proof backends are supplied, not autonomously invented; "
                   "the infinite-tail representation is not a new prime-distribution theorem. "
                   f"Independent checks: {mellin_kernels['verified_checks']}. All RH-strength uniform estimates remain unproved.\n"
                   f"Proof: mellin_kernel_proof.txt. Report: {mellin_kernels['run_directory']}/report.txt.\n")
    if kernel_correlations["status"] != "not_run":
        report += ("\nCOMPLETE SIGNED GRAM CORRELATIONS AND SQUAREFREE DENSITY CORRECTIONS\n\n"
                   "The search generates rational matrix observables, including learned, singular and indefinite metrics, "
                   "and promotes exact rational congruences with an equal-budget random-matrix ablation. Complete infinite actual inverse sums "
                   "give E_H=D_H+C_H. Products introduce general rational exponential rates and retain every signed cross coefficient.\n"
                   "Square-divisor inversion and partial summation prove |D_H(X)-A_H X|<=V_H sqrt(X) at every real X>0. "
                   "This signed arithmetic diagonal correction is a theorem. RH-strength signed cross-term bounds remain unproved.\n"
                   "The new density target is |D_H(N)-A_H N|<=C_q N^(1/4+epsilon/q^nu)*log(e+N)^d for every integer N and every q, "
                   "with a freely varying finite C_q. A certified Mellin multiplier prevents operator cancellation at ordinary denominator zeros. "
                   "Possible cancellation between zeta(s) and zeta(2s) is handled by a multiplicity-preserving reflection chain "
                   "rho -> 1-conjugate(rho)/2, whose heights halve and accumulate at nonzero zeta(2/3). "
                   "This is an all-height conditional bridge; the uniform quarter-power arithmetic estimate is not proved.\n"
                   f"Primary programs: {kernel_correlations['program_count']}; kinds: {kernel_correlations['program_counts_by_kind']}; "
                   f"primary growth hypotheses: {kernel_correlations['growth_hypotheses']}. "
                   f"Fresh RH-if-uniform survivors: {kernel_correlations['energy_RH_if_uniform_finite_survivors']} energy and "
                   f"{kernel_correlations['density_RH_if_uniform_finite_survivors']} density. "
                   f"Finite-passing globally false controls: {kernel_correlations['false_controls_finite_passes_analytically_rejected']}.\n"
                   "Fresh-q constants are calibrated only on frozen training scales and sealed before fresh final scales. "
                   "Conditional costs include singular pivots, the exact density main term, unit increments, local integrals, "
                   "native Gamma factors and the numerator-zeta factor needed for ordinary reciprocal recovery. "
                   "Finite tests, supplied proof backends and a true diagonal-only bound do not establish RH or new prime-distribution information. "
                   f"Independent checks: {kernel_correlations['verified_checks']}. "
                   f"Proof: kernel_correlation_proof.txt. Report: {kernel_correlations['run_directory']}/report.txt.\n")
    if lattice_synthesis["status"] != "not_run":
        report += ("\nTYPED LATTICE GLOBAL ESTIMATE SYNTHESIS AND FRACTIONAL DILATION BANKS\n\n"
                   "Actual generalized positions j*d^r have arithmetic profile zeta(s)/zeta(r*s). "
                   "A distinct unit reference has zeta(s)*zeta(r*s); their proof inputs cannot be interchanged. "
                   "Anonymous raw-response learning proposes rational kernels without receiving pole locations. "
                   "Rotated Gamma integrals and fully bounded Mellin contours automatically certify negative powers "
                   "after both reference residues are subtracted. These reference theorems have no RH consequence.\n"
                   "The actual signed density correction has a true weak all-scale exponent 1/r, which always corresponds "
                   "to ordinary-zeta exponent 1. A proved sign-loss barrier shows that taking absolute values after the "
                   "dilation rewrite cannot reach the critical exponent, even when actual squarefree support is retained. "
                   "That barrier is a limitation of this proof method, not a counterexample to a signed bound.\n"
                   "For 1<r<2, a certified cofinal critical bound confines right-half zeta zeros to exact finite "
                   "sets E_r={r^j/2:r^j<2}. The detector assembles banks with empty intersection. "
                   "Each bank would imply RH if every member's actual signed estimate were uniform. "
                   "All heights and multiplicities are covered; those uniform arithmetic estimates remain unproved. "
                   "Real operator roots and complete native complex-root exclusions broaden recovery without a "
                   "zero-free-kernel halfplane requirement.\n"
                   f"Programs: {lattice_synthesis['program_count']}; primary hypotheses: {lattice_synthesis['growth_hypotheses']}; "
                   f"global reference estimates: {lattice_synthesis['proved_reference_global_estimates']}; "
                   f"complementary banks: {lattice_synthesis['complementary_RH_banks']}, "
                   f"fresh finite passes: {lattice_synthesis['complementary_RH_banks_finite_passes']}. "
                   f"Independent checks: {lattice_synthesis['verified_checks']}. "
                   "A separate generic calibration checks square, cube, sixth and 10007th roots without changing selection. "
                   "Finite fits and reference-model proofs supply no new prime-distribution estimate.\n"
                   f"Proof: lattice_synthesis_proof.txt. Report: {lattice_synthesis['run_directory']}/report.txt.\n")
    if root_lattices["status"] != "not_run":
        report += ("\nNORMALIZED ARITHMETIC ROOTS AND SIGNED PROFILE LEARNING\n\n"
                   "Arithmetic dilations r>0 include square, cube and sixth roots. The index M is shared, X=M^r, "
                   "and kernel peaks are normalized; scale changes cannot create a stronger ordinary-zeta exponent. "
                   "The ordinary-index Mellin profile is W(z/r)*zeta(z/r)/(r*zeta(z)). "
                   "For 0<r<1, a hypothetical right-half zero repeatedly divides by r until its real part exceeds 1. "
                   "An all-height kernel certificate and an unproved cofinal critical signed bound are both required.\n"
                   "Anonymous moment recurrence inference is checked against held-out moments, then admitted only "
                   "with an exact factor-ledger certificate. A known actual signed collapse compiles to finite support "
                   "and proves rapid decay over every positive scale. Its arithmetic profile erases ordinary zeta "
                   "identically, so it has no RH consequence even when its kernel preserves right-half zeros.\n"
                   f"Programs: {root_lattices['program_count']}; primary hypotheses: {root_lattices['growth_hypotheses']}; "
                   f"recovering root bridges: {root_lattices['finite_division_escape_bridges']}; "
                   f"RH-if-uniform finite survivors: {len(root_lattices['RH_if_uniform_finite_survivors'])}. "
                   f"True signed rapid estimates in zero-erasing calibration: {root_lattices['proved_signed_actual_rapid_estimates']}. "
                   f"Compiled arithmetic promotions: {root_lattices['compiled_actual_arithmetic_promotions']}; "
                   f"false RH inferences rejected: {root_lattices['false_RH_inferences_rejected']}. "
                   f"Independent checks: {root_lattices['verified_checks']}.\n"
                   "Complete invisible counterfeit tails can pass finite tests while their uncancelled ordinary pole "
                   "disproves the global critical target. Actual recovering uniform estimates remain unproved. "
                   "Proof methods and bounded learning grammar were supplied; no new prime-distribution estimate is claimed.\n"
                   f"Proof: root_lattice_proof.txt. Report: {root_lattices['run_directory']}/report.txt.\n")
    if divisor_preconditioners["status"] != "not_run":
        report += ("\nDIVISOR PRECONDITIONING WITH RETAINED SIGNED ARITHMETIC\n\n"
                   "Logarithmic weights (log n)^a admit all positive rational orders, including square, cube and sixth roots. "
                   "Anonymous convolution features infer arithmetic identities; generic difference signatures describe "
                   "exact signs across every distinct-prime count. Noninteger orders retain alternating support "
                   "beyond any finite almost-prime cap. Those support laws are not distribution estimates.\n"
                   "A general triangular harmonic completion constructs divisor preconditioners for every integer jet. "
                   "Möbius inversion collapses only the preconditioned component and keeps the exact signed remainder. "
                   "The resulting actual weighted-prime and prime-power-convolution errors satisfy C*x at every real scale. "
                   "Ordinary zeta is retained; the proved power remains one.\n"
                   f"Global signed integer certificates: {divisor_preconditioners['integer_global_signed_certificates']}; "
                   f"learned universal convolution relations: {divisor_preconditioners['learned_universal_bell_relations']}; "
                   f"all-index sign certificates: {divisor_preconditioners['all_index_fractional_and_integer_sign_certificates']}; "
                   f"completion contexts with improved proved log loss: {divisor_preconditioners['completed_log_loss_improvements']}. "
                   f"Independent audit groups: {divisor_preconditioners['verified_checks']}.\n"
                   "Only the first integer jet has a verified all-ordinary-zero recovery argument. Higher derivatives "
                   "can mask zeros, and fractional branches require a full center. Supplied proof methods and known "
                   "Selberg calibration establish no RH-strength signed control or new independent prime-distribution estimate.\n"
                   f"Proof: divisor_preconditioner_proof.txt. Report: {divisor_preconditioners['run_directory']}/report.txt.\n")
    if branch_centers["status"] != "not_run":
        report += ("\nCOMPLETE FRACTIONAL CENTERS AND COFINAL SIGNED PARAMETER FAMILIES\n\n"
                   "Fractional logarithmic roots now have full real-cut centers. Their actual Mobius arithmetic and "
                   "ordinary nonreal zero information are retained. A cofinal parameter identity theorem and the "
                   "actual zeta pole prove conditional recovery at every ordinary height and multiplicity, "
                   "including finite signed filters whose weights sum to zero.\n"
                   f"Programs: {branch_centers['program_count']}; anonymous learned combinations: {branch_centers['anonymous_learned_combinations']}; "
                   f"new parameter-moment promotions: {branch_centers['parameter_moment_promotions']}; "
                   f"recovering zero-sum families: {branch_centers['zero_sum_weight_recovering_families']}. "
                   f"Fresh finite critical passes: {branch_centers['fresh_RH_if_uniform_finite_passes']} across "
                   f"{branch_centers['fresh_RH_if_uniform_programs']} programs.\n"
                   "The full centers use native Taylor coefficients with certified Cauchy tails and Rouche disks; "
                   "the checker uses separate coefficient division, a different disk, and direct integral anchors. "
                   "Complete continued observers are checked by fractional integrals of whole zeta. "
                   "Normalization, center, interpolation and gap costs are charged.\n"
                   f"Leading-only branch obstructions: {branch_centers['leading_only_branch_obstructions']}; "
                   f"independent audit groups: {branch_centers['verified_checks']}. "
                   "The proved all-real-scale signed power remains one with logarithmic loss one. "
                   "Critical family premises, independent new prime-distribution bounds and RH remain unproved.\n"
                   f"Proof: branch_center_proof.txt. Report: {branch_centers['run_directory']}/report.txt.\n")
    if rational_fractional_contracts["status"] != "not_run":
        report += ("\nUNBOUNDED RATIONAL FRACTIONAL EVALUATION CONTRACTS\n\n"
                   "A separate callable evaluator uses exact-rational exp/log powers to remove the native "
                   "unsigned 64-bit root-index limit. Precision-adaptive serialization preserves tiny parameter "
                   "differences, and exact native integer ceilings replace decimal truncation in large bound constants.\n"
                   f"Tested denominators: {rational_fractional_contracts['tested_rational_denominators']}. "
                   "Complete arithmetic, whole continued numerators, a normalized tiny-parameter high-pass filter, "
                   "full centers and a 201-digit weak-bound guard pass independent contracts. "
                   "These are numerical API regressions; candidates, fits, cases and frozen search selection stay unchanged.\n"
                   f"Evaluator: rational_fractional_evaluator.py. Verification: {rational_fractional_contracts['run_directory']}/rational_fractional_contract_verification.json.\n")
    if critical_defects["status"] != "not_run":
        report += ("\nCRITICAL SIGNED ENERGY DEFECT AND EXPLICIT DENSE RESIDUAL\n\n"
                   "The proof target is a one-sided bound A_2(2X)-4*A_2(X)<=B_epsilon*X^(2+epsilon) "
                   "for every cofinal positive epsilon and every dyadic X, with constants independent of X. "
                   "The exact unfiltered Mertens Mellin identity would then imply RH at every ordinary height "
                   "and off-critical multiplicity, without requiring critical-zero simplicity.\n"
                   "The diagonal defect is proved O(X^(3/2)). Primitive common-factor pairs with "
                   "max(n,m)/gcd(n,m)<=B have a proved C*X^(3/2)*B^(3/2)*(1+log B)^2 defect bound, "
                   "provided the same B is used in both scale terms. "
                   f"A frozen {critical_defects['cutoff_program_count']}-program rational grammar selected cutoff power "
                   f"{critical_defects['selected_cutoff_power']}, with component power {critical_defects['selected_component_power']} "
                   f"and log loss {critical_defects['selected_component_log_loss']}.\n"
                   "All other pair terms remain in an exact dense signed residual. Its required uniform bound "
                   "is unproved; the full absolute pair envelope still has power three. "
                   "A controlled sparse projection cannot substitute for the whole inequality.\n"
                   f"Fresh dyadic scales: {critical_defects['fresh_scales']}; fresh finite residual passes: "
                   f"{critical_defects['fresh_finite_residual_passes']}/{critical_defects['archived_finite_residual_estimates']}; "
                   f"independent audit groups: {critical_defects['verified_checks']}. "
                   "The common-factor construction and elementary density proof were supplied. "
                   "This guided bound audit establishes no new prime-sign distribution theorem or RH proof.\n"
                   f"Proof: critical_defect_proof.txt. Report: {critical_defects['run_directory']}/report.txt.\n")
    if divisor_duals["status"] != "not_run":
        report += ("\nDETECTOR CANDIDATES AND SEPARATE ANALYTICAL PROOF ATTEMPTS\n\n"
                   "The detector fits anonymous divisor responses and matrix kernels, promotes a zero-forcing "
                   "row mask, and compares an equal-slot random-mask ablation. Every lead retains the complete "
                   "signed energy defect and charges 4*X*D+Y*w(1). Its exact proof queue is sealed before final evaluation.\n"
                   f"Frozen programs: {divisor_duals['program_count']}; proof-queue candidates: {divisor_duals['proof_queue_candidates']}; "
                   f"fresh finite positive matrices: {divisor_duals['fresh_positive_matrices']}/{divisor_duals['fresh_matrix_cases']}; "
                   f"independent detector audit groups: {divisor_duals['verified_checks']}.\n"
                   "Native positivity is independently checked with exact integer Sylvester minors. Finite positivity "
                   "does not prove a cofinal-q all-scale matrix comparison. The unconditional q=1 calibration has energy power three.\n"
                   f"Detector report: {divisor_duals['run_directory']}/report.txt.\n")
    if dual_analytical_review["status"] != "not_run":
        report += (f"The separate analytical review disproves {dual_analytical_review['disproved_uniform_matrix_candidates']} "
                   f"uniform matrix templates and retains {dual_analytical_review['unresolved_uniform_matrix_candidates']} unresolved templates. "
                   "A positive-density set of uncontrolled tail rows gives a negative direction regardless of the Gram weight. "
                   "Quadratic Gram coefficients below 4/3 also fail via a full-tail vector. These are matrix-certificate "
                   "disproofs, not RH counterexamples. Original formulas and detector selections stay unchanged.\n"
                   "The complete nonunit Gram leads still require a uniform bound on the exact signed nullspace entry "
                   "D*Q(4X)-Delta(X). A conditional Schur buffer does not prove that arithmetic gap. "
                   "Prescribed polynomial growth of level constants is a grammar limitation; the general RH criterion "
                   "allows arbitrary finite constants at each epsilon. Feedback is reserved for a fresh search.\n"
                   f"Independent analytical audit groups: {dual_analytical_review['verified_checks']}. "
                   f"Proof: divisor_dual_analytic_proof.txt. Review: {dual_analytical_review['review_directory']}/report.txt. "
                   "No global RH-strength signed inequality has been proved.\n")
    if signed_gap_profiles["status"] != "not_run":
        report += ("\nINDEPENDENT CONSTANT LAWS AND ACTUAL LARGE-SCALE SIGNED GAPS\n\n"
                   "The new grammar separates cofinal rational exponent schedules from polynomial, exponential, "
                   "factorial and denominator-based constant laws. An existential per-level family keeps unseen "
                   "constants unknown. Rational logarithmic losses are allowed. Exact training constants and "
                   "candidate formulas are sealed before final evaluation and separate analytical attempts.\n"
                   f"Frozen profiles: {signed_gap_profiles['program_count']}; proof-queue candidates: {signed_gap_profiles['proof_queue_candidates']}; "
                   f"fresh X: {signed_gap_profiles['fresh_scales']}; actual coefficient cutoff: {signed_gap_profiles['fresh_actual_coefficient_cutoff']}. "
                   f"Finite half-gap passes: {signed_gap_profiles['fresh_half_gap_passes']}/{signed_gap_profiles['fresh_actual_observations']}; "
                   f"missing unseen constants: {signed_gap_profiles['fresh_missing_constants']}.\n"
                   "The target is the actual signed entry Delta(X)<=D(X,q)*Q(4X)/2. It remains unproved at every scale. "
                   "A delayed positive tail agrees with all development coefficients and has an analytically cubic defect; "
                   "complete actual divisor arithmetic distinguishes that counterfeit model.\n"
                   "Anonymous binary-prefix responses produce a minimum-energy polynomial. A separate generic "
                   "symbolic-difference and exchange argument proves the detected bound in every dimension. It "
                   "gives P(J)<=D*J as a necessary matrix condition for J omitted tail rows, without periodicity or position assumptions. "
                   "This is a global combinatorial estimate, not new signed prime control.\n"
                   "The constant-growth audit corrects an earlier scope implication: with epsilon=1/q and no log loss, "
                   "even positive polynomial powers r<1 would force simple critical zeros if proved. Growing constants "
                   "do not automatically remove extra multiplicity restrictions. Existential constants retain the unrestricted RH target.\n"
                   f"Independent detector groups: {signed_gap_profiles['verified_checks']}; analytical groups: {signed_gap_profiles['analytical_verified_checks']}. "
                   f"Proof and scope: signed_gap_profile_proof.txt. Report: {signed_gap_profiles['run_directory']}/report.txt. "
                   "No global critical signed arithmetic inequality or RH proof has been established.\n")
    if signed_gap_cofinal["status"] != "not_run":
        report += ("\nCOFINAL ACTUAL-ARITHMETIC COUNTEREXAMPLES TO FITTED GAP CANDIDATES\n\n"
                   "A separate analytical endpoint audit supersedes the earlier unresolved disposition of three "
                   "source half-gap templates. For a fixed dyadic X>=2, ceil(X^(1/d)) is exactly two whenever "
                   "d>=bit_length(X). With bounded fitted constants, this yields an exact eventual bound at that X. "
                   "The actual signed defect violates that bound at every sufficiently large parameter, so an "
                   "unknown starting q0 cannot remove the counterexample.\n"
                   f"Source candidates: {signed_gap_cofinal['candidate_count']}; half-gap claims disproved: "
                   f"{signed_gap_cofinal['disproved_uniform_actual_half_gap_candidates']}; complete dual-PSD comparisons disproved: "
                   f"{signed_gap_cofinal['disproved_complete_dual_PSD_candidates']}; fully charged global defect bounds disproved: "
                   f"{signed_gap_cofinal['disproved_fully_charged_global_defect_candidates']}; half-gap claims unresolved at this audit: "
                   f"{signed_gap_cofinal['unresolved_actual_half_gap_candidates']}.\n"
                   "These witnesses use the complete actual Mobius arithmetic. The half-gap, nullspace-PSD and "
                   "fully charged margins are audited separately. The source formulas, fitted constants, selection "
                   "and 704 available finite passes remain unchanged. Growing or unspecified constants are not "
                   "certified by this endpoint test. These are counterexamples to fitted inequalities, not RH.\n"
                   f"Independent audit groups: {signed_gap_cofinal['verified_checks']}. Proof: signed_gap_cofinal_proof.txt. "
                   f"Report: {signed_gap_cofinal['audit_directory']}/report.txt. No global critical signed arithmetic bound has been proved.\n")
    if candidate_reviews["status"] != "not_run":
        report += ("\nPARALLEL SOL 6.1 ANALYTICAL REVIEWS OF EXACT SIGNED-GAP CANDIDATES\n\n"
                   f"Requested model: {candidate_reviews['requested_reviewer_model']}; parallel batches: "
                   f"{candidate_reviews['reviewer_batches']}; exact candidates reviewed: {candidate_reviews['reviewed_candidate_count']}. "
                   "Assignments retain the frozen formulas and complete original evidence. Stable-id round-robin "
                   "allocation nominates no numerical winner. Reviews are sealed before independent checking.\n"
                   f"New globally refuted half-gap formulas: {candidate_reviews['verified_new_global_refutations']}; "
                   f"total source half-gap refutations: {len(candidate_reviews['all_refuted_candidate_ids'])}; "
                   f"current half-gap claims unresolved: {candidate_reviews['remaining_uniform_half_gap_claims']}.\n"
                   "The new exact actual arithmetic witness is dyadic X=2: A(2)=1, A(4)=10, Delta=6, Q(8)=6. "
                   "For every declared reciprocal exponent and EVERY q>=1, the root ceiling at two is exactly two. "
                   "Each refuted constant formula permits only 12*C<0.4. No choice of the starting q0 removes it. "
                   "These disprove particular fitted inequalities, not RH.\n"
                   "Provenance and typed actual counterexamples are independently checked. Unresolved reviewer prose, "
                   "conditional recurrence/multiplicity arguments and the auxiliary large development sieve are not "
                   "promoted to verified upper-bound proofs. Finite failures at excluded small q do not refute growing "
                   "or free-per-level cofinal claims. Original finite passes and formulas remain unchanged.\n"
                   f"Independent audit groups: {candidate_reviews['verified_checks']}; exact development diagnostics checked: "
                   f"{candidate_reviews['finite_development_observations_independently_checked']}. "
                   f"Report: {candidate_reviews['round_directory']}/report.txt. Proof scope: candidate_review_proof.txt. "
                   "No all-scale actual critical signed bound or RH proof has been established.\n")
    if inverse_prefix["status"] != "not_run":
        report += ("\nRESPONSE-INFERRED INVERSE PREFIX OPERATORS AND SIGNED SCALE POTENTIALS\n\n"
                   f"Learned inverse-factor arities: {inverse_prefix['training_arities']}; "
                   f"exact supports checked: {inverse_prefix['support_fits_checked']}; "
                   f"retained recurrence fits: {inverse_prefix['retained_recurrence_fits']}. "
                   "Anonymous response fitting receives no expected coefficient vector. A separate polynomial "
                   "proof admits the learned rule for every positive integer arity and every unit reference. "
                   "The exact signed inverse prefix through x is recovered from its values through u "
                   "whenever x<(u+1)^k; the endpoint is strict.\n"
                   f"Fresh generic reconstruction passes: {inverse_prefix['generic_final_reconstruction_passes']}/"
                   f"{inverse_prefix['generic_final_reconstruction_cases']}; promotion-disabled missing cases: "
                   f"{inverse_prefix['promotion_disabled_unseen_arity_cases_missing']}; "
                   f"actual full block reconstructions: {inverse_prefix['actual_full_block_reconstruction_passes']}/"
                   f"{inverse_prefix['actual_full_block_reconstruction_cases']}. "
                   "Actual primes are checked through complete independent Mobius arithmetic. Input compression "
                   "retains full divisibility geometry and reference costs; coefficient L1 cost is 2^k-1.\n"
                   f"Nonnegative potential programs: {inverse_prefix['potential_programs']}; queue leads: "
                   f"{inverse_prefix['potential_queue_candidates']}; fresh finite passes: "
                   f"{inverse_prefix['fresh_potential_finite_passes']}/{inverse_prefix['fresh_potential_finite_cases']}; "
                   f"unseen-level constants missing: {inverse_prefix['unseen_parameter_constants_missing']}. "
                   "Each potential is evaluated with its declared cutoff independently at X and 2X. "
                   "The supplied component norm gives a weak global envelope; it does not bound the full signed innovation.\n"
                   "The target is E(2X)+V(2X)-E(X)-V(X)<=C_q ceil(X^(1/q)) for every dyadic X and every "
                   "sufficiently large q, with fixed nonnegative V and scale-independent finite C_q. "
                   "If established for actual Mobius arithmetic, telescoping and unfiltered Mellin recovery imply RH. "
                   "That actual signed inequality remains unproved. Final scale design is visible to the worker; "
                   "final responses and seed-derived generic references are withheld until sealing. Actual "
                   "coefficients overlap earlier development. The pilot stays inside its declared resource budget; "
                   "generalized search missingness beyond that budget remains an extension task.\n"
                   f"Independent numeric groups: {inverse_prefix['verified_checks']}; analytical groups: "
                   f"{inverse_prefix['analytical_verified_checks']}. Report: {inverse_prefix['run_directory']}/report.txt. "
                   "Proof: inverse_prefix_proof.txt. No global actual critical signed control or RH proof established.\n")
    if inverse_prefix_reviews["status"] != "not_run":
        report += ("\nPARALLEL SOL 6.1 REVIEWS OF INVERSE PREFIX POTENTIALS\n\n"
                   f"Parallel reviewers: {inverse_prefix_reviews['parallel_reviewers']}; exact sealed leads: "
                   f"{inverse_prefix_reviews['reviewed_candidates']}; native component envelopes: "
                   f"{inverse_prefix_reviews['globally_bounded_potentials_verified']}. "
                   "The selected nonempty potentials tend to zero: the singleton is bounded by "
                   "4^(2/3)X^(-1/3), and the pair by 4/X+4^(2/3)X^(-1/3). "
                   "For bounded nonnegative V, the free-constant innovation claim is equivalent to "
                   "the baseline signed-defect claim after increasing each constant. The missing "
                   "actual arithmetic estimate remains the same.\n"
                   f"Exact actual witnesses: {[(r['X'], r['innovation']) for r in inverse_prefix_reviews['actual_signed_witnesses']]}; "
                   f"stored-level fitted inequalities refuted: {inverse_prefix_reviews['stored_level_inequalities_refuted']}. "
                   "Extending the common fitted constant 2^-64 to all large q is separately refuted. "
                   "Unknown later C_q and the starting q0 keep the original three existential "
                   "cofinal families unresolved. No frozen program or finite result was changed.\n"
                   f"Independent groups: {inverse_prefix_reviews['verified_checks']}; report: "
                   f"{inverse_prefix_reviews['review_directory']}/report.txt. "
                   "Proof: inverse_prefix_slot_review_proof.txt. Reviewer prose is retained separately; "
                   "only typed bounds and witnesses are admitted. Review arithmetic is development evidence, "
                   "not fresh validation. No actual all-scale signed bound or RH proof established.\n")
    if signed_arithmetic["status"] != "not_run":
        from signed_arithmetic_report import text_report as signed_arithmetic_text
        report += ("\nTYPED SIGNED ARITHMETIC AND COMPLETE SCALE STENCILS\n" +
                   signed_arithmetic_text(signed_arithmetic) +
                   f"Report: {signed_arithmetic['run_directory']}/report.txt. "
                   "Proof: signed_arithmetic_proof.txt.\n")
    if signed_arithmetic_reviews["status"] != "not_run":
        from signed_arithmetic_review_report import text_report as signed_review_text
        report += ("\nPARALLEL SIGNED ARITHMETIC REVIEWS AND DENSE RESIDUAL\n" +
                   signed_review_text(signed_arithmetic_reviews) +
                   f"Report: {signed_arithmetic_reviews['review_directory']}/report.txt.\n")
    if workflow_audit["status"] != "not_run":
        report += ("\nWORKFLOW RELIABILITY AND GENERIC SIGNED BOUND DISCOVERY AUDIT\n\n"
                   f"Contract tests passed: {workflow_audit['contract_test_cases']}. "
                   "Explicit safety wrappers propagate unavailable normalizers, preserve full degenerate fitted vectors "
                   "and unknown parameters, prevent sealed-run writes through the supported entry, and reject optimized "
                   "Python before dispatch/publication. Refutation exclusions are rederived from exact witnesses and "
                   "validated predecessors; reported counts and ID lists alone cannot remove a candidate.\n"
                   "The generic planner supports arbitrary sealed queue sizes, complete review preflight, hash-bound "
                   "collaboration receipts and atomic collection. Actual Sol6.1 dispatch uses the collaboration tools; "
                   "metadata alone does not authenticate runtime model identity. Global proof adjudication remains external.\n"
                   f"Generic all-integer signed-bound certificates: {workflow_audit['generic_signed_bound_certificates']}; "
                   f"genuinely unseen base5/6 signed instances: {workflow_audit['unseen_signed_generator_instances']}; "
                   f"delayed finite-passing controls globally rejected: {workflow_audit['delayed_finite_passing_control_candidates_rejected']}. "
                   "Learned moment coefficients transfer from bases2/3/4 without refitting; new instances have declared "
                   "digit/prefix probes and are sealed before larger dimensions. Full generic bounds are admitted "
                   "by an exact block-cancellation proof, while positive and unsigned controls fail.\n"
                   "This calibration supplies its arithmetic generator class, feature dictionary and proof method. "
                   "Numeric blindness is function/data-flow separation, not adversarial OS isolation. It does not "
                   "demonstrate general-purpose theorem discovery or a success probability for RH. Current actual-zeta "
                   "leads trained on negative-only innovations and fitted constants without the earliest dyadic boundaries. "
                   "Bounded corrections do not resolve the missing actual signed cancellation.\n"
                   f"Audit report: {workflow_audit['audit_directory']}/report.txt. "
                   "The workflow is a tested research tool; no actual all-scale RH-strength signed estimate has been proved.\n")
    if signed_correlation["status"] != "not_run":
        report += ("\nEXPLICIT SIGNED CORRELATION AND MOMENT DEFECT OBLIGATIONS\n\n"
                   "The exact quadratic decomposition is A_2(X)=D(X)+C_off(X). "
                   "The diagonal has the proved bound 0<=D(X)<=2*S^2*X^2 at every integer scale. "
                   "The off-diagonal sum retains actual Mobius signs and an explicit arithmetic kernel. "
                   "A uniform C_off(X)<=K X^2 would suffice for RH when the multiplier is globally nonzero.\n"
                   "Alternatively a proved recurrence A_2(2X)-4*A_2(X)<=B X^2 at every dyadic scale "
                   "would permit A_2(X)=O(X^2 log X) and still suffice for RH. These signed premises "
                   "remain unproved. The diagnostic uses already inspected exact windows, with no "
                   "reselection or fresh validation claim.\n"
                   "Proofs: signed_correlation_proof.txt and signed_recurrence_proof.txt. "
                   f"Exact obligations: {signed_correlation['source_run']}/correlation_obligations.json.\n")
    report += "\nSIGNED FAMILY: AUTOMATIC ALL-INTEGER GAP CERTIFICATES\n\n"
    if compensated["status"] == "not_run":
        report += "Not yet published. Run --compensated-only to audit existing signed-family evidence.\n"
    else:
        best = compensated["automatically_selected_operator"]
        report += (f"Origin: {compensated['discovery_origin']}. "
                   "This guided family is reported separately from autonomous generic-language discovery.\n"
                   f"Proved all-composite bounds: {len(compensated['proved_global_estimates'])}. "
                   f"Actual counterexamples: {len(compensated['counterexamples'])}. "
                   f"Retained numerical leads: {len(compensated['numerical_leads'])}.\n"
                   f"Independent exact polynomial certificates: {compensated['independent_polynomial_certificates_checked']}.\n")
        if best is not None:
            report += (f"Automatically selected parameters: {best['left']}, {best['right']}; "
                       f"prime coefficient 1; |B(n)|<={best['composite_absolute_bound']} "
                       "for every composite n, without a prime-size cutoff.\n")
        native = compensated["complete_native_zeta_audit"]
        report += (f"Complete independent native-zeta groups: {native['groups']}, "
                   f"for parameters {native['left']}, {native['right']}.\n"
                   "Prime counts, signed cancellation, the RH continuation target and historical novelty "
                   "remain separate unresolved gates. The main 150-group count is unchanged.\n"
                   "Detailed report: ../compensated-shift-results/report.txt.\n"
                   "Recheck existing certificates: ../.venv/bin/python run_expanded_probe.py --compensated-only.\n")
        winner_native = compensated["automatic_winner_native_zeta_audit"]
        if winner_native["status"] != "not_run":
            report += (f"Automatic winner: {winner_native['groups']} further independently checked complete "
                       f"native-zeta groups for parameters {winner_native['left']}, {winner_native['right']}. "
                       "Cases were sampled after automatic selection closed; they do not retune that selection.\n")
    (output_dir / "report.txt").write_text(report)
    print(report)


if __name__ == "__main__":
    main()
