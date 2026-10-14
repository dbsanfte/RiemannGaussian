#!/usr/bin/env python3
"""Generate, run, and validate a known-operator discovery calibration.

Run: python3 benchmark.py
Requires Python 3.10+ and its standard library only. No packages are installed.

The search subprocess gets training.json only, with anonymous case IDs and
impulse responses. This evaluator knows the targets, so this is label-blind
software separation, not an independently blinded experiment. The search's
linear/bilinear model class and grammar are declared in search.py. Calibration
does not establish completeness, novelty, or anything about RH.

Outputs: anonymous training data, private evaluation data, learned programs,
held-out scores, grammar ablations, and a human-readable report. Exact integer
and rational arithmetic removes round-off from the first calibration. Extending
this to zeta observations will require a separate numerical-error study.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import subprocess
import sys
from functools import lru_cache
from pathlib import Path

from search import apply_kernel, kernel


TARGETS = [
    ("additive_convolution", "Additive convolution", 2, "known"),
    ("multiplicative_convolution", "Dirichlet convolution", 2, "known"),
    ("forward_difference", "Forward finite difference", 1, "known"),
    ("divisor_sum", "Divisor-sum transform", 1, "known"),
    ("quotient_profile", "Floor quotient profile", 1, "known"),
    ("divisor_inverse", "Mobius inversion", 1, "known"),
    ("random_unary", "Random unary kernel", 1, "negative"),
    ("random_binary", "Random binary kernel", 2, "negative"),
    ("finite_mimic", "Finite-training mimic", 1, "negative"),
    ("nonlinear_mimic", "Nonlinear impulse mimic", 1, "negative"),
]


@lru_cache(maxsize=None)
def mobius(integer):
    sign, divisor = 1, 2
    while divisor * divisor <= integer:
        if integer % divisor == 0:
            integer //= divisor
            sign *= -1
            if integer % divisor == 0:
                return 0
        divisor += 1
    return -sign if integer > 1 else sign


def coefficient(name, seed, training_size, n, i, j=None):
    """Ground truth is confined to the evaluator, never the learner."""
    if name == "additive_convolution":
        return int(n == i + j)
    if name == "multiplicative_convolution":
        return int(n == i * j)
    if name == "forward_difference":
        return int(i == n + 1) - int(i == n)
    if name in {"divisor_sum", "finite_mimic", "nonlinear_mimic"}:
        baseline = int(n % i == 0)
        if name == "finite_mimic" and n == i and n > training_size:
            baseline += 7
        return baseline
    if name == "quotient_profile":
        return n // i
    if name == "divisor_inverse":
        return mobius(n // i) if n % i == 0 else 0
    if name in {"random_unary", "random_binary"}:
        payload = f"{name}:{seed}:{n}:{i}:{j}".encode()
        return int.from_bytes(hashlib.blake2b(payload, digest_size=4).digest(), "big") % 7 - 3
    raise ValueError(name)


def oracle(name, seed, training_size, inputs, output_size):
    result = []
    for n in range(1, output_size + 1):
        if len(inputs) == 1:
            observed = sum(coefficient(name, seed, training_size, n, i) * entry
                           for i, entry in enumerate(inputs[0], 1))
        else:
            observed = sum(coefficient(name, seed, training_size, n, i, j) * a * b
                           for i, a in enumerate(inputs[0], 1)
                           for j, b in enumerate(inputs[1], 1))
        # This term vanishes on every unit impulse, but exposes the learner's
        # linearity assumption when the evaluator supplies dense inputs.
        if name == "nonlinear_mimic" and n == 1 and len(inputs[0]) > 1:
            observed += inputs[0][0] * inputs[0][1]
        result.append(observed)
    return result


def write_json(path, data):
    path.write_text(json.dumps(data, indent=2) + "\n")


def generate(seed, repeats):
    rng = random.Random(seed)
    targets = list(TARGETS)
    rng.shuffle(targets)
    training = {"schema": 1, "cases": {}}
    private = {"seed": seed, "cases": {}}
    for name, label, arity, category in targets:
        identifier = f"case_{rng.getrandbits(64):016x}"
        input_size, output_size = (12, 12) if arity == 1 else (6, 36)
        # Query the oracle on unit impulses. Response tensors are flattened in
        # (output n, input i [, input j]) order, matching search.py's convention.
        responses = [None] * (output_size * input_size ** arity)
        for i in range(input_size):
            for j in (range(input_size) if arity == 2 else (None,)):
                a = [int(index == i) for index in range(input_size)]
                inputs = [a] if arity == 1 else [
                    a, [int(index == j) for index in range(input_size)]]
                observed = oracle(name, seed, input_size, inputs, output_size)
                for n, entry in enumerate(observed):
                    offset = n * input_size ** arity + i * (input_size if arity == 2 else 1)
                    responses[offset + (j if arity == 2 else 0)] = entry
        training["cases"][identifier] = {"arity": arity, "input_size": input_size,
                                          "output_size": output_size,
                                          "basis_responses": responses}
        evaluations = []
        sizes = [input_size] + ([24, 40, 64] if arity == 1 else [10, 14, 20])
        for size in sizes:
            out_size = size if arity == 1 else size * size
            # Include a full nonzero input, sparse inputs, and fresh signed data.
            for trial in range(repeats):
                if trial == 0:
                    inputs = [[1] * size for _ in range(arity)]
                else:
                    inputs = [[rng.randint(-5, 5) if trial != 1 or rng.random() < .3
                               else 0 for _ in range(size)] for _ in range(arity)]
                evaluations.append({"split": "same_size" if size == input_size else "larger_size",
                                    "input_size": size, "output_size": out_size,
                                    "inputs": inputs,
                                    "output": oracle(name, seed, input_size, inputs, out_size)})
        private["cases"][identifier] = {"name": name, "label": label,
                                         "category": category, "evaluations": evaluations}
    return training, private


def evaluate(learned, training, private):
    cases = {}
    for identifier, info in private["cases"].items():
        prediction = learned["cases"][identifier]
        program = prediction["program"]
        scores = {split: {"passed": 0, "total": 0, "max_abs_error": 0}
                  for split in ("same_size", "larger_size")}
        cache = {}
        if program is not None:
            arity = training["cases"][identifier]["arity"]
            for example in info["evaluations"]:
                shape = (example["input_size"], example["output_size"])
                failure = None
                if shape not in cache:
                    try:
                        cache[shape] = kernel(program, arity, *shape)
                    except ValueError as error:
                        cache[shape] = error
                if isinstance(cache[shape], ValueError):
                    failure = str(cache[shape])
                    error_value = None
                else:
                    values = apply_kernel(cache[shape], example["inputs"], example["output_size"])
                    error_value = max(abs(actual - expected)
                                      for actual, expected in zip(values, example["output"]))
                score = scores[example["split"]]
                score["total"] += 1
                score["passed"] += int(failure is None and error_value == 0)
                if failure:
                    score["evaluation_error"] = failure
                elif error_value > score["max_abs_error"]:
                    # JSON uses floats only for reporting; acceptance above is exact.
                    score["max_abs_error"] = float(error_value)
        accepted = (program is not None and all(
            score["total"] > 0 and score["passed"] == score["total"]
            for score in scores.values()))
        cases[identifier] = {"label": info["label"], "category": info["category"],
                             **prediction, "validation": scores, "accepted": accepted}
    return {"grammar": learned["grammar"], "cases": cases,
            "known_recovered": sum(case["accepted"] for case in cases.values()
                                   if case["category"] == "known"),
            "known_total": sum(case["category"] == "known" for case in cases.values()),
            "negative_controls_accepted": sum(case["accepted"] for case in cases.values()
                                              if case["category"] == "negative"),
            "negative_controls_total": sum(case["category"] == "negative" for case in cases.values())}


def run_search(directory, training_path, flag=None):
    suffix = "full" if flag is None else flag.removeprefix("--")
    destination = directory / f"learned_{suffix}.json"
    command = [sys.executable, str(Path(__file__).with_name("search.py")),
               str(training_path), "--output", str(destination)]
    if flag:
        command.append(flag)
    completed = subprocess.run(command, check=True, capture_output=True, text=True)
    print(f"{suffix}: {completed.stdout.strip()}", flush=True)
    return json.loads(destination.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=20261006)
    parser.add_argument("--repeats", type=int, default=4)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "results")
    args = parser.parse_args()
    if args.repeats < 2:
        parser.error("--repeats must be at least 2")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    training, private = generate(args.seed, args.repeats)
    training_path = args.output_dir / "training.json"
    write_json(training_path, training)
    write_json(args.output_dir / "private_evaluation.json", private)
    print("Generated anonymous impulse observations and separate fresh-input evaluations", flush=True)
    results = {}
    for flag in (None, "--no-multiply", "--no-inverse"):
        suffix = "full" if flag is None else flag.removeprefix("--")
        learned = run_search(args.output_dir, training_path, flag)
        results[suffix] = evaluate(learned, training, private)
        write_json(args.output_dir / f"scores_{suffix}.json", results[suffix])
    full = results["full"]
    lines = ["Known arithmetic operator discovery calibration", f"Seed: {args.seed}",
             "Exact arithmetic; anonymous impulse responses; separate dense and larger-size evaluation.",
             "Model assumptions: unary linear / binary bilinear; limited index-expression grammar.",
             "The evaluator knows the targets; this is not an independently blinded experiment.", ""]
    for case in sorted(full["cases"].values(), key=lambda case: case["label"]):
        scores = case["validation"]
        same, larger = scores["same_size"], scores["larger_size"]
        verdict = "ACCEPT" if case["accepted"] else ("REJECT" if case["program"] else "ABSTAIN")
        lines += [f"{case['label']}: {verdict}", f"  Rule: {case['rule']}",
                  f"  Fresh inputs at training size: {same['passed']}/{same['total']}",
                  f"  Larger sizes: {larger['passed']}/{larger['total']}"]
    lines += ["", f"Full grammar: {full['known_recovered']}/{full['known_total']} known operators recovered; "
              f"{full['negative_controls_accepted']}/{full['negative_controls_total']} controls accepted."]
    for suffix in ("no-multiply", "no-inverse"):
        result = results[suffix]
        lines.append(f"{suffix}: {result['known_recovered']}/{result['known_total']} known operators recovered; "
                     f"{result['negative_controls_accepted']}/{result['negative_controls_total']} controls accepted.")
    lines += ["", "A recovery means finite calibration success within this declared grammar.",
              "No completeness, novelty, or RH conclusion follows from these results."]
    report = "\n".join(lines) + "\n"
    (args.output_dir / "report.txt").write_text(report)
    print(report)
    if full["known_recovered"] != full["known_total"] or full["negative_controls_accepted"]:
        raise SystemExit("Calibration failed: inspect scores_full.json")


if __name__ == "__main__":
    main()
