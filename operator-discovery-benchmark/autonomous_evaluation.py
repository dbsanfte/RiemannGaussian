#!/usr/bin/env python3
"""Own discovery observations, prime labels, independent targets and final data.

Prime labels never enter coefficient production. The selector receives declared
empirical summary scores on development scales; fresh final cases arrive only
after sealing. Targets are anonymous until evaluation is complete.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import random
import secrets
import sys

from autonomous_grammar import evaluate, encode, decode, digest, expanded, cost
from autonomous_protocol import validate_spec


def read(p): return json.loads(Path(p).read_text())


def write(p, x): Path(p).write_text(json.dumps(x, indent=2, allow_nan=False) + "\n")


def cases(spec, split, seed=None):
    rng = random.Random(seed if seed is not None else spec["data"][split + "_seed"])
    out = []
    for k, (N, kind) in enumerate(spec["data"][split]):
        inputs = []
        for slot in (0, 1):
            if kind == "zeta_coefficients": arr = [[1, 1, 0, 1] for _ in range(N)]
            else:
                arr = []
                for i in range(N):
                    a = Q(rng.randrange(-5, 6), rng.randrange(1, 5))
                    b = Q(rng.randrange(-3, 4), rng.randrange(1, 5)) if kind == "complex" else Q(0)
                    if kind == "sparse" and rng.random() < .8: a, b = Q(0), Q(0)
                    arr.append([a.numerator, a.denominator, b.numerator, b.denominator])
            inputs.append(arr)
        out.append({"id": f"{split}_{k}", "N": N, "kind": kind, "inputs": inputs})
    return out


def isprime(n):
    if n < 2: return False
    d = 2
    while d * d <= n:
        if n % d == 0: return False
        d += 1
    return True


def bucket(x):
    a, b = Q(x[0], x[1]), Q(x[2], x[3])
    if not a and not b: return "zero"
    if a == 1 and not b: return "one"
    if a < 0 and not b: return "negative_real"
    return "other"


def prime_metrics(outputs, examples):
    # Conditional information avoids calling the supplied labels a discovery.
    # A bucket has to repeat: an injective output like n is not a prime decoder.
    rows = []
    for y, ex in zip(outputs, examples):
        if ex["kind"] == "zeta_coefficients" and len(y) == ex["N"]:
            for n, x in enumerate(y, 1):
                if n >= 2: rows.append(((n % 2, n % 3), bucket(x), isprime(n)))
    def entropy(groups):
        total = len(rows)
        ans = 0.
        for group in groups.values():
            counts = Counter(group)
            ans += len(group) / total * -sum((v / len(group)) * math.log2(v / len(group)) for v in counts.values())
        return ans
    if not rows: return {"conditional_information_bits": 0., "labelled_observations": 0, "new_information_proved": False}
    old = defaultdict(list); new = defaultdict(list)
    for baseline, value, label in rows:
        old[baseline].append(label); new[baseline, value].append(label)
    return {"conditional_information_bits": max(0., entropy(old) - entropy(new)), "labelled_observations": len(rows),
            "baseline": "residues mod 2 and 3", "output_feature": "four fixed scalar buckets",
            "label_provenance": "evaluator trial-division primality at every labelled index; no producer calls",
            "new_information_proved": False}


def observe(spec, records, macros, examples):
    out = []
    for r in records:
        ys = []; errors = []; ops = []
        for ex in examples:
            try:
                y, used = evaluate(r["program"], [[decode(x) for x in arr] for arr in ex["inputs"]], macros=macros,
                                   operations=spec["resources"]["operations_per_case"], inverse_max=spec["resources"]["matrix_inverse_max_dimension"])
                ys.append([encode(x) for x in y]); errors.append(None); ops.append(used)
            except (ValueError, ZeroDivisionError) as e:
                ys.append([]); errors.append(str(e)); ops.append(None)
        out.append({"id": r["id"], "outputs": ys, "errors": errors, "operation_counts": ops,
                    "prime_metrics": prime_metrics(ys, examples), "producer_prime_or_factor_queries": 0})
    return out


def collect(spec, batch, split):
    if batch["protocol_sha256"] != digest(spec): raise ValueError("batch/protocol mismatch")
    examples = cases(spec, split)
    rows = observe(spec, batch["programs"], batch["macros"], examples)
    return {"protocol_sha256": digest(spec), "batch_sha256": digest(batch), "split": split,
            "examples": examples, "records": rows, "candidate_batch_frozen_before_observation": True,
            "prime_oracle_owner": "evaluator", "producer_prime_or_factor_queries": 0}


def independent_scalar(t, n, i, N):
    # Deliberately separate interpreter for synthetic-target kernel generation.
    # Only the declared first-order scalar-kernel subset is eligible.
    o = t[0]
    if o == "v": return {"n": n, "i": i, "N": N}[t[1]]
    if o == "int": return t[1]
    if o == "q": return Q(t[1], t[2])
    if o == "embed": return Q(independent_scalar(t[1], n, i, N))
    if o == "indicator": return Q(bool(independent_scalar(t[1], n, i, N)))
    a = independent_scalar(t[1], n, i, N); b = independent_scalar(t[2], n, i, N)
    if o == "ia": return a + b
    if o == "is": return a - b
    if o == "im": return a * b
    if o == "iq": return a // b
    if o == "ir": return a % b
    if o == "eq": return a == b
    if o == "le": return a <= b
    if o == "lt": return a < b
    raise ValueError("target kernel outside declared subset")


def oracle(target, inputs):
    x = inputs[0]; N = len(x); name = target["kind"]
    out = []
    for n in range(1, N + 1):
        total = Q(0)
        for i, value in enumerate(x, 1):
            if name in {"divisor_sum", "finite_mimic", "nonlinear_mimic"}: k = int(n % i == 0)
            elif name == "identity": k = int(n == i)
            elif name == "prefix_sum": k = int(i <= n)
            elif name == "floor_profile": k = n // i
            else:
                k = sum((Q(a, b) * independent_scalar(t, n, i, N) for t, a, b in target["pieces"]), Q(0))
            if name == "finite_mimic" and n == i and n > target["threshold"]: k += 7
            total += k * value
        out.append(total)
    if name == "nonlinear_mimic" and N >= 2: out[0] += x[0] * x[1]
    return out


def benchmark_create(spec, batch):
    from autonomous_search import calibration_dictionary
    dictionary = calibration_dictionary(spec, batch)
    entropy = secrets.token_hex(24); rng = random.Random(entropy)
    examples = []
    for N in spec["calibration"]["training_sizes"]:
        examples.append({"N": N, "inputs": [[[1, 1, 0, 1]] * N, [[1, 1, 0, 1]] * N]})
        for k in range(N):
            examples.append({"N": N, "inputs": [[[int(i == k), 1, 0, 1] for i in range(N)], [[1, 1, 0, 1]] * N]})
    targets = [("named_calibration", {"kind": name}) for name in ("identity", "divisor_sum", "prefix_sum", "floor_profile")]
    for _ in range(spec["calibration"]["synthetic_targets"]):
        a, b = rng.sample(dictionary, 2)
        wa, wb = rng.choice([-3, -2, -1, 1, 2, 3]), rng.choice([-3, -2, -1, 1, 2, 3])
        targets.append(("independently_sampled_synthetic", {"kind": "random_signed_kernel", "pieces": [[a["program"][1][1], wa, 1], [b["program"][1][1], wb, rng.choice([1, 2, 3])]]}))
    targets.extend([("negative_control", {"kind": "finite_mimic", "threshold": max(spec["calibration"]["training_sizes"])}),
                    ("negative_control", {"kind": "nonlinear_mimic"})])
    rng.shuffle(targets); public = {}; private = {}
    for category, target in targets:
        identifier = "anonymous_" + f"{rng.getrandbits(80):020x}"
        public[identifier] = {"responses": [[encode(x) for x in oracle(target, [[decode(x) for x in a] for a in ex["inputs"]])] for ex in examples]}
        private[identifier] = {"category": category, "target": target}
    return ({"protocol_sha256": digest(spec), "examples": examples, "cases": public, "labels_or_target_formulas_shared": False},
            {"protocol_sha256": digest(spec), "entropy_seed": entropy, "cases": private,
             "target_generation": "separate evaluator, OS entropy after language freeze, independently interpreted scalar kernels",
             "scope": "in-language randomized benchmark; not independent mathematical novelty"})


def relation_final(rel, batch, values):
    from autonomous_search import flatten, successful
    by_id = {r["id"]: r for r in values}
    if not all(successful(by_id[k]) for k, _, _ in rel["terms"]):
        return {"id": rel["id"], "status": "unresolved_comparison", "reason": "declared domain/resource failure", "passed": False}
    terms = [(Q(a, b), flatten(by_id[k])) for k, a, b in rel["terms"]]
    err = max((abs(sum((a * v[i] for a, v in terms), Q(0))) for i in range(len(terms[0][1]))), default=Q(0))
    return {"id": rel["id"], "status": "finite_identity_verified" if err == 0 else "counterexample_found",
            "passed": err == 0, "residual": [err.numerator, err.denominator], "all_scale_claim": False}


def final(spec, directory):
    directory = Path(directory); seal = read(directory / "seal.json")
    for name, expected in seal["files"].items():
        if digest(read(directory / name)) != expected: raise ValueError("sealed file changed: " + name)
    private = read(directory / "private_benchmark_targets.json")
    if digest(private) != seal["private_targets_committed_sha256"]: raise ValueError("private target commitment changed")
    final_path = directory / "final_cases.json"
    if final_path.exists(): raise ValueError("final cases already inspected; start a fresh frozen run")
    entropy = secrets.token_hex(24)
    examples = cases(spec, "final", entropy)
    write(final_path, {"source_seal_sha256": digest(seal), "entropy_seed": entropy, "examples": examples,
                       "created_after_seal": True, "adaptation_allowed": False})
    layers = {}; ablation = {}
    for label in ("baseline", "adaptive", "ablation"):
        batch = read(directory / (label + "_batch.json")); archive = read(directory / (label + "_archive.json"))
        needed = {r["id"] for r in archive["archive"]}
        for rel in archive["relations"]:
            if rel["validation_passed"]: needed.update(k for k, _, _ in rel["terms"])
        records = [r for r in batch["programs"] if r["id"] in needed]
        values = observe(spec, records, batch["macros"], examples)
        ids = {r["id"]: r for r in values}
        rows = [{"id": r["id"], "status": "numerical_lead" if all(e is None for e in ids[r["id"]]["errors"]) else "unresolved_comparison",
                 "final_domain_passed": all(e is None for e in ids[r["id"]]["errors"]), "errors": ids[r["id"]]["errors"],
                 "all_scale_theorem_proved": False, "new_prime_information_proved": False} for r in archive["archive"]]
        rels = [relation_final(rel, batch, values) for rel in archive["relations"] if rel["validation_passed"]]
        layers[label] = {"programs": rows, "relations": rels, "records": values,
                         "final_domain_survivors": sum(r["final_domain_passed"] for r in rows), "unsupported_leads_retained": len(rows)}
        good_ids = {r["id"] for r in rows if r["final_domain_passed"]}
        new = [r for r in archive["archive"] if r["id"] in good_ids]
        ablation[label] = {"generation_attempts": spec["adaptive"]["candidates_per_batch"] if label != "baseline" else len(batch["programs"]),
                           "admitted_programs": len(batch["programs"]), "generation_rejections": len(batch["generation_rejections"]),
                           "final_domain_survivors": len(new), "distinct_final_behaviors": len({digest(ids[r["id"]]["outputs"]) for r in new}),
                           "maximum_validated_expanded_cost": max((r["expanded_cost"] for r in new), default=0),
                           "total_declared_final_operations": sum(x for r in values for x in r["operation_counts"] if x is not None)}
    learned = read(directory / "benchmark_learned.json"); rng = random.Random(entropy + "benchmark")
    benchmark_examples = []
    for N in spec["calibration"]["final_sizes"]:
        for kind in ("rational", "complex"):
            arr = [[Q(rng.randrange(-6, 7), rng.randrange(1, 5)), Q(rng.randrange(-4, 5), rng.randrange(1, 5)) if kind == "complex" else Q(0)] for _ in range(N)]
            xs = [[a.numerator, a.denominator, b.numerator, b.denominator] for a, b in arr]
            benchmark_examples.append({"N": N, "kind": kind, "inputs": [xs, [[1, 1, 0, 1]] * N]})
    benchmark = []
    for k, info in private["cases"].items():
        p = learned["cases"][k]["program"]; errors = []
        for ex in benchmark_examples:
            inputs = [[decode(x) for x in a] for a in ex["inputs"]]
            target = [encode(x) for x in oracle(info["target"], inputs)]
            if p is None: errors.append("no admissible training fit"); continue
            try:
                got, _ = evaluate(p, inputs)
                errors.append(None if [encode(x) for x in got] == target else "fresh dense/cross-scale counterexample")
            except ValueError as e: errors.append(str(e))
        benchmark.append({"id": k, "category": info["category"], "target": info["target"], "learned_program": p,
                          "training_match": learned["cases"][k]["exact_training_match"], "accepted": all(e is None for e in errors), "errors": errors})
    return {"protocol_sha256": digest(spec), "seal_sha256": digest(seal), "final_cases_sha256": digest(read(final_path)),
            "final_examples": examples, "benchmark_final_examples": benchmark_examples, "layers": layers,
            "promotion_ablation": ablation, "benchmarks": benchmark,
            "named_recovered": sum(r["accepted"] for r in benchmark if r["category"] == "named_calibration"),
            "named_total": sum(r["category"] == "named_calibration" for r in benchmark),
            "synthetic_recovered": sum(r["accepted"] for r in benchmark if r["category"] == "independently_sampled_synthetic"),
            "synthetic_total": sum(r["category"] == "independently_sampled_synthetic" for r in benchmark),
            "false_controls_accepted": sum(r["accepted"] for r in benchmark if r["category"] == "negative_control"),
            "final_evaluation_used_for_selection": False, "verified_new_operators": [],
            "analytic_theorem_proved": False, "new_independent_prime_distribution_estimate_proved": False}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("mode", choices=["collect", "benchmark-create", "final"])
    for k in ("spec", "batch", "output", "private", "run-dir"): p.add_argument("--" + k, type=Path)
    p.add_argument("--split", choices=["discovery", "validation"])
    a = p.parse_args(); spec = read(a.spec); validate_spec(spec)
    if a.mode == "collect": result = collect(spec, read(a.batch), a.split)
    elif a.mode == "benchmark-create":
        result, private = benchmark_create(spec, read(a.batch)); write(a.private, private)
    else: result = final(spec, a.run_dir)
    write(a.output, result)
    print("Evaluator", a.mode, a.split or "", "records", len(result.get("records", [])))


if __name__ == "__main__": main()
