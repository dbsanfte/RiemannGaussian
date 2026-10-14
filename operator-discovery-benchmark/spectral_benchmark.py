#!/usr/bin/env python3
"""Recover coefficient operations from spectral measurements alone.

Run: python3 spectral_benchmark.py

The learner receives anonymous complex feature weights and measured responses
to pairs of impulses. It does not receive output coefficient tables, transform
names, or convolution rules. We observe products of two finite generating
functions and search for a coefficient operation that predicts those products.
This still supplies the input/output relationship to investigate; it is not
discovery from an unperturbed zeta function alone.
"""

from __future__ import annotations

import argparse
import cmath
import itertools
import json
import math
import random
import subprocess
import sys
from decimal import Decimal, localcontext
from pathlib import Path

from search import apply_kernel, cost, kernel, make_dictionary, render, scaled


def encode(values):
    return [[entry.real, entry.imag] for entry in values]


def weights(family, parameter, size):
    if family == "dirichlet":
        return [cmath.exp(-parameter * math.log(n)) for n in range(1, size + 1)]
    return [parameter ** n for n in range(1, size + 1)]


def observe(inputs, feature_weights):
    transformed = [sum(entry * feature_weights[i] for i, entry in enumerate(a))
                   for a in inputs]
    return transformed[0] * transformed[1]


def signature(entries, size, samples):
    width = size * size
    predictions = []
    for sample in samples:
        features = [complex(*entry) for entry in sample["weights"]]
        predictions.extend(sum(entries[n * width + ij] * features[n]
                               for n in range(len(features))) for ij in range(width))
    return predictions


def residual(expected, actual):
    return max(abs(y - prediction) / max(abs(y), 1e-12)
               for y, prediction in zip(expected, actual))


def learn(case):
    size, out_size = case["input_size"], case["output_size"]
    expected = [complex(*entry) for sample in case["samples"]
                for entry in sample["responses"]]
    dictionary = make_dictionary(2, size, out_size, multiply=True)
    columns = [(program, signature(entries, size, case["samples"]))
               for program, entries in dictionary]
    matches = []
    tested = 0
    for program, column in columns:
        for coefficient in (-3, -2, -1, 1, 2, 3):
            tested += 1
            error = residual(expected, [coefficient * entry for entry in column])
            if error < 1e-10:
                matches.append((scaled(program, coefficient), error))
    for (left, x), (right, y) in itertools.combinations(columns, 2):
        for u, v in itertools.product((-3, -2, -1, 1, 2, 3), repeat=2):
            tested += 1
            error = residual(expected, [u * a + v * b for a, b in zip(x, y)])
            if error < 1e-10:
                program = {"kind": "sum", "terms": [
                    {"coefficient": u, "program": left},
                    {"coefficient": v, "program": right}]}
                matches.append((program, error))
    matches.sort(key=lambda item: (cost(item[0]), json.dumps(item[0])))
    program, error = matches[0] if matches else (None, None)
    return {"program": program, "rule": render(program, 2),
            "training_max_relative_error": error, "matching_programs": len(matches),
            "candidate_models_checked": tested}


def decimal_check(family, program, inputs, out_size):
    with localcontext() as context:
        context.prec = 80
        if family == "dirichlet":
            features = [(-Decimal("1.35") * Decimal(n).ln()).exp()
                        for n in range(1, out_size + 1)]
        else:
            features = [Decimal("0.98") ** n for n in range(1, out_size + 1)]
        expected = observe(inputs, features)
        coefficients = apply_kernel(kernel(program, 2, len(inputs[0]), out_size), inputs, out_size)
        predicted = sum(Decimal(entry) * feature for entry, feature in zip(coefficients, features))
        relative = abs(predicted - expected) / max(abs(expected), Decimal("1e-50"))
        return str(relative), relative < Decimal("1e-70")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "spectral-results")
    parser.add_argument("--learn-file", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.learn_file is not None:
        if args.output is None:
            parser.error("--learn-file needs --output")
        data = json.loads(args.learn_file.read_text())
        learned = {identifier: learn(case) for identifier, case in data["cases"].items()}
        args.output.write_text(json.dumps(learned, indent=2) + "\n")
        return

    args.output_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(20261006)
    specs = [
        ("dirichlet", [complex(1.15, .7), complex(1.45, -2.3), complex(2.1, 4.7)]),
        ("ordinary", [.98 * cmath.exp(.31j), cmath.exp(1.17j), .97 * cmath.exp(-2.13j)]),
    ]
    training, private = {"cases": {}}, {}
    for family, parameters in specs:
        identifier = f"case_{rng.getrandbits(64):016x}"
        size, out_size = 6, 36
        samples = []
        for parameter in parameters:
            features = weights(family, parameter, out_size)
            # For basis inputs, the measured function product is the product of
            # the two input fingerprints. No inverse transform is computed.
            samples.append({"weights": encode(features),
                            "responses": encode([features[i] * features[j]
                                                 for i in range(size) for j in range(size)])})
        training["cases"][identifier] = {"input_size": size, "output_size": out_size,
                                          "samples": samples}
        private[identifier] = family
    train_path = args.output_dir / "training.json"
    learned_path = args.output_dir / "learned.json"
    train_path.write_text(json.dumps(training, indent=2) + "\n")
    subprocess.run([sys.executable, str(Path(__file__).resolve()), "--learn-file", str(train_path),
                    "--output", str(learned_path)], check=True)
    learned = json.loads(learned_path.read_text())
    scores, lines = {}, ["Recovery from products of finite generating functions", ""]
    for identifier, family in private.items():
        result = learned[identifier]
        program = result["program"]
        passed, total, max_error = 0, 0, 0.0
        if program is None:
            raise SystemExit(f"No spectral rule recovered for {identifier}")
        for size in (6, 10, 14, 20):
            out_size = size * size
            entries = kernel(program, 2, size, out_size)
            for trial in range(4):
                inputs = [[1] * size for _ in range(2)] if trial == 0 else [
                    [rng.randint(-5, 5) for _ in range(size)] for _ in range(2)]
                parameter = complex(rng.uniform(1.05, 2.5), rng.uniform(-8, 8)) if family == "dirichlet" else (
                    rng.uniform(.97, 1.0) * cmath.exp(rng.uniform(-math.pi, math.pi) * 1j))
                features = weights(family, parameter, out_size)
                expected = observe(inputs, features)
                coefficients = apply_kernel(entries, inputs, out_size)
                predicted = sum(entry * feature for entry, feature in zip(coefficients, features))
                error = abs(predicted - expected) / max(1.0, abs(expected))
                total += 1
                passed += int(error < 1e-10)
                max_error = max(max_error, error)
        inputs = [[1] * 20, [1] * 20]
        decimal_error, decimal_pass = decimal_check(family, program, inputs, 400)
        accepted = passed == total and decimal_pass
        scores[identifier] = {"family": family, **result, "fresh_spectral_checks": {"passed": passed,
            "total": total, "max_error_normalized_by_max_one_abs_expected": max_error},
            "precision_80_decimal_relative_error": decimal_error, "accepted": accepted}
        lines += [f"{family}: {'ACCEPT' if accepted else 'REJECT'}", f"  {result['rule']}",
                  f"  Fresh inputs, sizes, and spectral parameters: {passed}/{total}",
                  f"  80-digit relative residual: {decimal_error}"]
    lines += ["", "These are finite generating-function experiments, not analytic-continuation tests.",
              "Pointwise multiplication and the family of perturbations were supplied.",
              "The learned rule connects function products to their coefficient operation."]
    (args.output_dir / "scores.json").write_text(json.dumps(scores, indent=2) + "\n")
    report = "\n".join(lines) + "\n"
    (args.output_dir / "report.txt").write_text(report)
    print(report)
    if not all(case["accepted"] for case in scores.values()):
        raise SystemExit("Spectral calibration failed")


if __name__ == "__main__":
    main()
