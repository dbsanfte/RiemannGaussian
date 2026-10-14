#!/usr/bin/env python3
"""Frozen guided calibration of general jets and actual prime information."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import random
import secrets
import subprocess
import sys
import flint
from estimate_grammar import inverse_one_prefix
from parameter_jets import (VERSION, real, power_parameter_jet,
    logarithmic_kernel_zero_jet, family_zero_jet, strict_cutoff,
    root_count_decode)
from pole_neutral_grammar import coefficients, kernel

BASE = Path(__file__).resolve().parent
CODE = ["parameter_jets.py", "parameter_jet_audit.py", "check_parameter_jets.py",
        "parameter_jet_report.py", "parameter_jet_proof.txt"]


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":"),
                                   allow_nan=False).encode()).hexdigest()


def write(path, data):
    Path(path).write_text(json.dumps(data, indent=2, allow_nan=False) + "\n")


def serial(value):
    return (value + flint.arb(0, (real(Q(1, 2**160)) * (1+abs(value))).upper())).str(45)


def produce(directory):
    spec = read(directory / "protocol.json")
    for name, expected in spec["code_sha256"].items():
        assert sha(BASE/name) == expected
    assert not (directory/"jet_data.json").exists()
    # This is a guided calibration with no adaptive selection or held-out
    # discovery claim. Draw irregular inputs after freezing the source plan.
    seed = secrets.randbits(128)
    rng = random.Random(seed)
    points = sorted(set(map(Q, spec["boundary_points"])) |
                    {Q(rng.randint(17, 2*spec["cutoff"]-1), 2) for _ in range(4)})
    cases = {"seed": str(seed), "points": list(map(str, points)),
             "created_after_protocol_frozen": True,
             "protocol_sha256": digest(spec)}
    write(directory/"cases.json", cases)
    flint.ctx.prec = spec["precision_bits"]
    flint.ctx.cap = spec["jet_order"] + 1
    N, order = spec["cutoff"], spec["jet_order"]
    mu = list(map(Q, inverse_one_prefix(N)))
    jets = {str(a): [[str(v) for v in row] for row in power_parameter_jet(mu, a, order)]
            for a in map(Q, spec["coefficient_centres"])}
    generic = []
    for _ in range(spec["generic_inputs"]):
        f = [Q(0), Q(1)] + [Q(rng.randint(-3, 3), rng.randint(1, 4))
                            for _ in range(spec["generic_cutoff"]-1)]
        a = Q(rng.randint(-3, 3), rng.randint(1, 4))
        generic.append({"input": list(map(str, f)), "centre": str(a),
                        "jets": [[str(v) for v in row] for row in power_parameter_jet(f, a, order)]})
    kernels = [{"u": str(u), "kappa": str(k),
                "jets": list(map(serial, logarithmic_kernel_zero_jet(real(u), order, k)))}
               for u in map(Q, spec["kernel_u"]) for k in map(Q, spec["kernel_shifts"])]
    d = list(map(Q, jets["0"][1]))
    lambda_coefficients = [-v for v in d]
    family = []
    for x in points:
        for q, r in ((Q(q), Q(r)) for q, r in spec["path_slopes"]):
            jet = family_zero_jet(mu, x, order, q, r)
            family.append({"x": str(x), "coefficient_slope": str(q),
                           "kernel_slope": str(r), "jets": list(map(serial, jet))})
    decoded = [{"x": str(x), "prime_count_strict": str(root_count_decode(lambda_coefficients, mu, x)),
                "prime_power_count_strict": str(sum(lambda_coefficients[2:strict_cutoff(x)+1], Q(0)))}
               for x in points]
    quotients = []
    for denominator in spec["probe_denominators"]:
        a = Q(1, denominator)
        nu = coefficients(a, N)
        for x in points:
            value = sum((real(nu[n])*kernel(a, 1, real(x/n).log())
                         for n in range(1, strict_cutoff(x)+1)), flint.arb(0))
            quotient = (value-1)/real(a)
            quotients.append({"a": str(a), "x": str(x), "value": serial(value),
                              "difference_quotient": serial(quotient)})
    result = {"scope": "guided_parameter_jet_and_prime_recovery_calibration",
              "protocol_sha256": digest(spec), "cases_sha256": digest(cases),
              "coefficient_jets": jets, "generic_jets": generic, "kernel_jets": kernels,
              "family_jets": family, "decoded_counts": decoded,
              "finite_difference_probes": quotients,
              "universal_operator_identity_argument": "parameter_jet_proof.txt",
              "coupled_RH_sufficient_target": {
                  "premise": "For every real x>=2 and every 0<a<=a0, |G_a(x)-1|<=C*a*sqrt(x)*(1+log(x))^L",
                  "C_and_a0_finite_positive_L_fixed_nonnegative_integer": True,
                  "uniform_premise_proved": False},
              "new_prime_distribution_bound_proved": False,
              "uniform_RH_sufficient_signed_controls_verified": [], "RH_proved": False}
    write(directory/"jet_data.json", result)
    print("Produced general jets and guided prime recovery; no uniform signed estimate asserted", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--source-run", type=Path, required=True)
    args = parser.parse_args()
    directory, source = args.run_dir.resolve(), args.source_run.resolve()
    if directory.exists():
        raise FileExistsError("A new frozen calibration directory is required")
    from pole_neutral_report import summary
    summary(source)
    directory.mkdir(parents=True)
    inherited = read(source/"protocol.json")["code_sha256"]
    spec = {"grammar_version": VERSION,
            "scope": "guided_calibration_no_independent_discovery_claim",
            "source_run": str(source),
            "source_verification_sha256": sha(source/"verification.json"),
            "code_sha256": dict(inherited, **{n: sha(BASE/n) for n in CODE}),
            "cutoff": 512, "jet_order": 3, "precision_bits": 384,
            "coefficient_centres": ["-1/2", "0", "1/3", "1"],
            "generic_inputs": 4, "generic_cutoff": 48,
            "boundary_points": ["129/128", "255/128", "2", "257/128", "3", "4", "8", "16", "64", "128"],
            "kernel_u": ["1/64", "1/3", "2", "7"], "kernel_shifts": ["-1/2", "0", "1"],
            "path_slopes": [["1", "1"], ["2", "1"], ["1", "2"]],
            "probe_denominators": [32, 128, 512],
            "producer_prime_or_factor_oracle": False,
            "named_special_function_dependencies": ["Gamma Euler product", "DLMF 5.7.3-4", "DLMF 6.6.1"],
            "no_finite_to_uniform_promotion": True}
    write(directory/"protocol.json", spec)
    produce(directory)
    subprocess.run([sys.executable, str(BASE/"check_parameter_jets.py"),
                    "--run-dir", str(directory)], check=True, cwd=BASE)
    from parameter_jet_report import publish
    publish(directory)


if __name__ == "__main__":
    main()
