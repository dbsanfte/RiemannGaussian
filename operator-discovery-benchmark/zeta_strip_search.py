#!/usr/bin/env python3
"""Search short relations between actual zeta measurements in and near the strip.

The feature library and coefficient budgets are explicit. Completion by Gamma
is supplied as a calibration representation, not learned. No zero locations or
RH labels are used in training. Candidate coefficients are fixed before tests
at higher precision and previously unseen points/heights. This is an exact-rule
search within a small library, not a general search over all arithmetic.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
from pathlib import Path

import mpmath as mp
import numpy as np


AFFINE = [(1, -1), (1, 0), (1, 1), (2, -1), (2, 0), (2, 1), (-1, 0), (-1, 1)]
PAIR_COEFFICIENTS = (-3, -2, -1, -.5, .5, 1, 2, 3)
TRIPLE_COEFFICIENTS = (-3, -2, -1, 1, 2, 3)


def affine_name(a, b):
    return f"zeta({a}*s{b:+d})"


def completion(s):
    return s * (s - 1) * mp.power(mp.pi, -s / 2) * mp.gamma(s / 2) / 2


def features(s):
    values = {affine_name(a, b): mp.zeta(a * s + b) for a, b in AFFINE}
    central = values[affine_name(1, 0)]
    result = dict(values)
    result.update({f"zeta(s)*{name}": central * entry for name, entry in values.items()
                   if name != affine_name(1, 0)})
    result.update({"zeta(s)^2": central ** 2, "s*zeta(s)": s * central,
                   "s^2*zeta(s)": s * s * central,
                   "zeta_prime(s)": mp.zeta(s, derivative=1),
                   "zeta_second(s)": mp.zeta(s, derivative=2),
                   "xi(s)": completion(s) * central,
                   "xi(1-s)": completion(1 - s) * values[affine_name(-1, 1)],
                   "conj(zeta(conj(s)))": mp.conj(mp.zeta(mp.conj(s))),
                   "1": mp.mpf(1), "s": s, "s^2": s * s})
    return result


def points(rng, size, real_range, height_range):
    return [[str(round(rng.uniform(*real_range), 8)),
             str(round(rng.uniform(*height_range) * (-1 if index % 2 else 1), 8))]
            for index in range(size)]


def dataset(sample_points, digits):
    mp.mp.dps = digits
    rows, names, records = [], None, []
    for index, (real, imag) in enumerate(sample_points):
        values = features(mp.mpc(real, imag))
        names = list(values)
        rows.append([complex(entry) for entry in values.values()])
        records.append({"s": [real, imag], "values": {
            name: [mp.nstr(mp.re(value), digits), mp.nstr(mp.im(value), digits)]
            for name, value in values.items()}})
        if (index + 1) % 16 == 0:
            print(f"Strip observations: {index + 1}/{len(sample_points)} at {digits} digits", flush=True)
    return names, np.asarray(rows, dtype=complex).T, records


def scan(names, data):
    candidates, nearest, tested = [], [], 0

    def record(indices, coefficients, errors):
        nonlocal tested
        tested += len(coefficients)
        best_index = int(np.argmin(errors))
        best = {"features": [names[index] for index in indices],
                "coefficients": list(coefficients[best_index]),
                "training_relative_residual": float(errors[best_index])}
        nearest.append(best)
        for index in np.flatnonzero(errors < 1e-10):
            candidates.append({"features": [names[item] for item in indices],
                               "coefficients": list(coefficients[index]),
                               "training_relative_residual": float(errors[index])})

    pair_values = np.asarray(PAIR_COEFFICIENTS)[:, None]
    for i, j in itertools.combinations(range(len(names)), 2):
        residuals = np.abs(data[i] + pair_values * data[j]) / np.maximum(
            np.abs(data[i]) + np.abs(pair_values * data[j]), 1e-300)
        record((i, j), [(1, coefficient) for coefficient in PAIR_COEFFICIENTS],
               np.max(residuals, axis=1))
    pairs = list(itertools.product(TRIPLE_COEFFICIENTS, repeat=2))
    left_values = np.array([pair[0] for pair in pairs])[:, None]
    right_values = np.array([pair[1] for pair in pairs])[:, None]
    for i, j, k in itertools.combinations(range(len(names)), 3):
        residuals = np.abs(data[i] + left_values * data[j] + right_values * data[k]) / np.maximum(
            np.abs(data[i]) + np.abs(left_values * data[j]) + np.abs(right_values * data[k]), 1e-300)
        record((i, j, k), [(1, a, b) for a, b in pairs], np.max(residuals, axis=1))
    nearest.sort(key=lambda item: item["training_relative_residual"])
    return candidates, nearest[:8], tested


def validate(candidates, records):
    mp.mp.dps = 110
    result = []
    for candidate in candidates:
        maximum, errors = mp.mpf(0), []
        for record in records:
            values = [mp.mpc(*record["values"][name]) for name in candidate["features"]]
            terms = [coefficient * value for coefficient, value in zip(candidate["coefficients"], values)]
            error = abs(sum(terms)) / max(sum(abs(term) for term in terms), mp.mpf("1e-300"))
            maximum = max(maximum, error)
            errors.append(mp.nstr(error, 12))
        result.append({**candidate, "held_out_max_relative_residual": mp.nstr(maximum, 12),
                       "held_out_points": len(records), "accepted": bool(maximum < mp.mpf("1e-80")),
                       "held_out_residuals": errors})
    return result


def controls(sample_points):
    mp.mp.dps = 110
    rho = mp.mpc("0.65", "17.3")
    roots = [rho, 1 - rho, mp.conj(rho), 1 - mp.conj(rho)]
    normalization = mp.fprod(2 - root for root in roots)

    def synthetic(s):
        return completion(s) * mp.zeta(s) * mp.fprod(s - root for root in roots) / normalization

    maxima = {"actual_xi_reflection": mp.mpf(0), "perturbed_integer_coefficient_reflection": mp.mpf(0),
              "synthetic_off_axis_zero_reflection": mp.mpf(0)}
    for real, imag in sample_points:
        s = mp.mpc(real, imag)
        actual = (completion(s) * mp.zeta(s), completion(1 - s) * mp.zeta(1 - s))
        perturbed = (completion(s) * (mp.zeta(s) + mp.power(3, -s) / 5),
                     completion(1 - s) * (mp.zeta(1 - s) + mp.power(3, s - 1) / 5))
        fake = (synthetic(s), synthetic(1 - s))
        for name, (left, right) in zip(maxima, (actual, perturbed, fake)):
            error = abs(left - right) / max(abs(left) + abs(right), mp.mpf("1e-300"))
            maxima[name] = max(maxima[name], error)
    return {"reflection_relative_residuals": {name: mp.nstr(value, 12) for name, value in maxima.items()},
            "synthetic_added_zeros": [[mp.nstr(mp.re(root), 12), mp.nstr(mp.im(root), 12)] for root in roots],
            "synthetic_description": "xi(s) times a normalized polynomial with a conjugate/reflected quartet of off-axis zeros",
            "scope": "The synthetic function is not zeta and need not have zeta's arithmetic or growth properties"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "zeta-results")
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    rng = random.Random(2026100603)
    training_points = points(rng, 40, (-.4, 1.7), (1.3, 32))
    holdout_points = points(rng, 12, (-.8, 2.2), (2, 35)) + points(rng, 16, (-1.2, 2.5), (40, 160))
    names, training, training_records = dataset(training_points, 75)
    print(f"Searching short relations among {len(names)} measured features", flush=True)
    candidates, nearest, tested = scan(names, training)
    _, _, holdout_records = dataset(holdout_points, 110)
    evaluated = validate(candidates, holdout_records)
    phase_rng = np.random.default_rng(2026100604)
    randomized = training * np.exp(1j * phase_rng.uniform(-np.pi, np.pi, training.shape))
    phase_candidates, _, _ = scan(names, randomized)
    countermodels = controls(holdout_points)
    result = {"feature_library": names, "feature_count": len(names), "models_checked": tested,
              "grammar": {"pair_coefficients": PAIR_COEFFICIENTS,
                          "triple_coefficients": TRIPLE_COEFFICIENTS,
                          "max_terms": 3, "first_coefficient": 1,
                          "completed_xi_representation_supplied": True},
              "training_digits": 75, "holdout_digits": 110,
              "training_points": len(training_points), "holdout_points": len(holdout_points),
              "training_observations": training_records, "holdout_observations": holdout_records,
              "candidates": evaluated, "nearest_training_relations": nearest,
              "random_phase_controls_training_matches": len(phase_candidates),
              "countermodels": countermodels}
    (args.output_dir / "strip_search.json").write_text(json.dumps(result, indent=2) + "\n")
    lines = ["Search on analytically continued zeta values", "",
             f"Features: {len(names)}; candidate relations: {tested}",
             f"Training: {len(training_points)} points, 75 digits, |t| <= 32",
             f"Validation: {len(holdout_points)} fresh points, 110 digits, heights reaching 160", ""]
    for candidate in evaluated:
        text = " + ".join(f"{coefficient}*{name}" for coefficient, name in zip(
            candidate["coefficients"], candidate["features"]))
        lines += [f"{'ACCEPT' if candidate['accepted'] else 'REJECT'}: {text} = 0",
                  f"  Maximum held-out relative residual: {candidate['held_out_max_relative_residual']}"]
    lines += ["", f"Independent random-phase control matches: {len(phase_candidates)}",
              "Reflection control residuals:"]
    lines += [f"  {name}: {value}" for name, value in countermodels["reflection_relative_residuals"].items()]
    lines += ["", "Reflection and conjugation are classical symmetries; completion was supplied as a representation.",
              "The off-axis-zero control preserves reflection, so that symmetry alone cannot establish RH.",
              "No zero locations or RH labels were used in fitting; the synthetic zeros are controls only.",
              "A failure to find a relation applies only to this explicit finite feature library."]
    report = "\n".join(lines) + "\n"
    (args.output_dir / "strip_report.txt").write_text(report)
    print(report)


if __name__ == "__main__":
    main()
