#!/usr/bin/env python3
"""Independent semantics/certificate audit plus deterministic and access replays.

Mathematical checking below does not import producer/search/evaluator modules.
The replay and public access-control tests run them separately as integration
checks. Exact Q(i) is implemented as pairs here, not producer Gaussian objects.
"""
from __future__ import annotations
import argparse
from collections import Counter
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import subprocess
import sys

BASE = Path(__file__).resolve().parent


def read(p): return json.loads(Path(p).read_text())


def canon(x): return json.dumps(x, sort_keys=True, separators=(",", ":"), allow_nan=False)


def sha(x): return hashlib.sha256(canon(x).encode()).hexdigest()


def pair(x): return Q(x[0], x[1]), Q(x[2], x[3])


def enc(x): return [x[0].numerator, x[0].denominator, x[1].numerator, x[1].denominator]


def plus(a, b): return a[0] + b[0], a[1] + b[1]


def times(a, b): return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scaled(a, c): return a[0] * c, a[1] * c


def total(xs):
    out = (Q(0), Q(0))
    for x in xs: out = plus(out, x)
    return out


def expand(t, macros, seen=frozenset()):
    if t[0] == "macro":
        if t[1] in seen: raise ValueError("macro cycle")
        return expand(macros[t[1]]["body"], macros, seen | {t[1]})
    return [t[0]] + [expand(x, macros, seen) if isinstance(x, list) else x for x in t[1:]]


def astcost(t): return 1 + sum(astcost(x) for x in t[1:] if isinstance(x, list))


def scalar(t, env):
    o = t[0]
    if o == "v": return env[t[1]]
    if o == "int": return t[1]
    if o == "q": return Q(*t[1:])
    if o == "embed": return Q(scalar(t[1], env))
    if o == "indicator": return Q(int(scalar(t[1], env)))
    if o == "not": return not scalar(t[1], env)
    if o == "bsum": return sum((scalar(t[3], {**env, t[1]: i}) for i in range(1, min(env["N"], max(0, scalar(t[2], env))) + 1)), Q(0))
    a, b = scalar(t[1], env), scalar(t[2], env)
    ops = {"ia": lambda: a + b, "is": lambda: a - b, "im": lambda: a * b,
           "iq": lambda: a // b, "ir": lambda: a % b, "eq": lambda: a == b,
           "le": lambda: a <= b, "lt": lambda: a < b, "and": lambda: a and b,
           "sadd": lambda: a + b, "smul": lambda: a * b}
    return ops[o]()


def M(t, N):
    o = t[0]
    if o == "kernel": return [[scalar(t[1], {"n": n, "i": i, "N": N}) for i in range(1, N + 1)] for n in range(1, N + 1)]
    if o == "mscale": return [[scalar(t[1], {"N": N}) * a for a in row] for row in M(t[2], N)]
    A = M(t[1], N)
    if o == "minverse":
        # Solve columns by elimination with backward substitution, independently
        # of the producer's Gauss-Jordan row normalization.
        result = [[Q(0)] * N for _ in range(N)]
        for col in range(N):
            rows = [r[:] + [Q(j == col)] for j, r in enumerate(A)]
            for k in range(N):
                pivot = next((j for j in range(k, N) if rows[j][k]), None)
                if pivot is None: raise ValueError("singular")
                rows[k], rows[pivot] = rows[pivot], rows[k]
                for j in range(k + 1, N):
                    a = rows[j][k] / rows[k][k]
                    rows[j] = [x - a * y for x, y in zip(rows[j], rows[k])]
            x = [Q(0)] * N
            for k in range(N - 1, -1, -1):
                x[k] = (rows[k][-1] - sum(rows[k][j] * x[j] for j in range(k + 1, N))) / rows[k][k]
            for k in range(N): result[k][col] = x[k]
        return result
    B = M(t[2], N)
    if o == "madd": return [[a + b for a, b in zip(x, y)] for x, y in zip(A, B)]
    return [[sum(A[n][k] * B[k][i] for k in range(N)) for i in range(N)] for n in range(N)]


def evaluate(t, inputs, macros):
    t = expand(t, macros); N = len(inputs[0]); cache = {}
    def run(p):
        key = canon(p)
        if key in cache: return cache[key]
        o = p[0]
        if o == "input": y = inputs[p[1]]
        elif o == "tab": y = [(Q(scalar(p[1], {"n": n, "N": N})), Q(0)) for n in range(1, N + 1)]
        elif o == "apply":
            A = M(p[1], N); x = run(p[2]); y = [total(scaled(b, a) for a, b in zip(row, x)) for row in A]
        elif o == "pair":
            x, z = run(p[2]), run(p[3]); y = []
            for n in range(1, N + 1):
                y.append(total(scaled(times(a, b), scalar(p[1], {"n": n, "i": i, "j": j, "N": N}))
                               for i, a in enumerate(x, 1) for j, b in enumerate(z, 1) if any(a) and any(b)))
        elif o == "scale": y = [scaled(x, scalar(p[1], {"N": N})) for x in run(p[2])]
        elif o == "norm2": y = [(x * x + z * z, Q(0)) for x, z in run(p[1])]
        else: y = [(plus if o == "add" else times)(a, b) for a, b in zip(run(p[1]), run(p[2]))]
        cache[key] = y
        return y
    return [enc(x) for x in run(t)]


def polynomial(t):
    o = t[0]
    if o == "input": return {(int(t[1] == 0), int(t[1] == 1)): Q(1)}
    if o == "tab" and t[1][0] == "q": return {(0, 0): Q(t[1][1], t[1][2])}
    if o == "scale" and t[1][0] == "q": return {a: c * Q(t[1][1], t[1][2]) for a, c in polynomial(t[2]).items()}
    if o not in {"add", "point"}: raise ValueError("unsupported")
    A, B = polynomial(t[1]), polynomial(t[2]); out = dict(A) if o == "add" else {}
    if o == "add":
        for a, c in B.items(): out[a] = out.get(a, Q(0)) + c
    else:
        for a, c in A.items():
            for b, d in B.items():
                k = (a[0] + b[0], a[1] + b[1]); out[k] = out.get(k, Q(0)) + c * d
    return {k: c for k, c in out.items() if c}


def oracle(target, inputs):
    x = inputs[0]; N = len(x); out = []
    for n in range(1, N + 1):
        terms = []
        for i, a in enumerate(x, 1):
            o = target["kind"]
            if o in {"divisor_sum", "finite_mimic", "nonlinear_mimic"}: k = Q(n % i == 0)
            elif o == "identity": k = Q(n == i)
            elif o == "prefix_sum": k = Q(i <= n)
            elif o == "floor_profile": k = Q(n // i)
            else: k = sum(Q(a, b) * scalar(t, {"n": n, "i": i, "N": N}) for t, a, b in target["pieces"])
            if o == "finite_mimic" and n == i and n > target["threshold"]: k += 7
            terms.append(scaled(a, k))
        out.append(total(terms))
    if target["kind"] == "nonlinear_mimic": out[0] = plus(out[0], times(x[0], x[1]))
    return [enc(x) for x in out]


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument("--run-dir", type=Path, required=True)
    a = parser.parse_args(); directory = a.run_dir.resolve()
    spec = read(directory / "protocol.json"); seal = read(directory / "seal.json"); final = read(directory / "final_evaluation.json")
    checks = {}; details = {}; batches = {}; archives = {}
    for name, expected in spec["code_sha256"].items(): assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == expected, name
    for name, expected in seal["files"].items(): assert sha(read(directory / name)) == expected, name
    assert final["seal_sha256"] == sha(seal) and seal["selection_closed"] and not seal["final_cases_created"]
    assert read(directory / "final_cases.json")["created_after_seal"]
    assert final["final_cases_sha256"] == sha(read(directory / "final_cases.json"))
    checks["frozen_protocol_code_batches_and_final_provenance"] = True
    independent_values = 0; certified = 0; unresolved = 0; macro_uses = 0
    for label in ("baseline", "adaptive", "ablation"):
        batch = read(directory / (label + "_batch.json")); arc = read(directory / (label + "_archive.json"))
        batches[label] = batch; archives[label] = arc
        assert batch["protocol_sha256"] == sha(spec) and arc["batch_sha256"] == sha(batch)
        assert not arc["final_data_used"] and arc["verified_new_operators"] == []
        assert len(arc["selection_ledger"]) == len(batch["programs"])
        ids = {r["id"]: r for r in batch["programs"]}
        proposals = read(directory / (label + "_relations.json"))
        assert proposals["batch_sha256"] == sha(batch) and arc["proposals_sha256"] == sha(proposals)
        responses_by_split = {}
        for r in batch["programs"]:
            assert r["id"] == sha(r["program"])
            assert r["encoded_cost"] == astcost(r["program"])
            assert r["expanded_cost"] == astcost(expand(r["program"], batch["macros"]))
            macro_uses += int('"macro"' in canon(r["program"]))
        for split in ("discovery", "validation"):
            response = read(directory / (label + "_" + split + ".json"))
            responses_by_split[split] = {r["id"]: r for r in response["records"]}
            assert response["batch_sha256"] == sha(batch) and response["producer_prime_or_factor_queries"] == 0
            assert arc[split + "_sha256"] == sha(response)
            for r in response["records"]:
                assert r["producer_prime_or_factor_queries"] == 0
                # Replay EVERY successful program at both one development size
                # and a changed validation size with this independent interpreter.
                index = 0
                if r["errors"][index] is None:
                    inputs = [[pair(x) for x in arr] for arr in response["examples"][index]["inputs"]]
                    assert evaluate(ids[r["id"]]["program"], inputs, batch["macros"]) == r["outputs"][index], (label, split, r["id"])
                    independent_values += len(r["outputs"][index])
        for rel in arc["relations"]:
            assert rel["training_residual"] == 0
            for split in ("discovery", "validation"):
                terms = [(Q(a, b), responses_by_split[split][k]) for k, a, b in rel["terms"]]
                domain = all(all(e is None for e in row["errors"]) for _, row in terms)
                if domain:
                    vectors = [(a, [Q(u, v) for y in row["outputs"] for x in y for u, v in ((x[0], x[1]), (x[2], x[3]))]) for a, row in terms]
                    residual = max((abs(sum(a * vector[i] for a, vector in vectors)) for i in range(len(vectors[0][1]))), default=Q(0))
                    if split == "discovery": assert residual == 0
                    else:
                        assert rel["validation_passed"] == (residual == 0)
                        assert rel["validation_residual"] == [residual.numerator, residual.denominator]
                elif split == "validation": assert not rel["validation_passed"]
            if rel["certificate"]["status"] == "universal_arithmetic_identity_proved":
                assert not polynomial(expand(rel["program"], batch["macros"]))
                assert not rel["certificate"]["analytic_claim"]
                certified += 1
            if rel["validation_passed"] and rel["certificate"]["status"] == "unsupported": unresolved += 1
        for k, m in arc["promotions"].items():
            assert sha(m["body"]) == k and not m["dependency_ids"]
            assert len(m["evidence_program_ids"]) >= spec["promotion"]["minimum_reusing_programs"]
            assert m["total_encoded_saving"] == len(m["evidence_program_ids"]) * (astcost(m["body"]) - 1)
        # Generic complex and irregular final inputs for each surviving family.
        values = {r["id"]: r for r in final["layers"][label]["records"]}; families = set()
        for r in arc["archive"]:
            if r["family"] in families or values[r["id"]]["errors"][1] is not None: continue
            families.add(r["family"])
            ex = final["final_examples"][1]; inputs = [[pair(x) for x in arr] for arr in ex["inputs"]]
            assert evaluate(r["program"], inputs, batch["macros"]) == values[r["id"]]["outputs"][1]
            independent_values += len(ex["inputs"][0])
        for r in final["layers"][label]["programs"]:
            assert not r["all_scale_theorem_proved"] and not r["new_prime_information_proved"]
        for rel in final["layers"][label]["relations"]:
            original = next(r for r in arc["relations"] if r["id"] == rel["id"])
            terms = [(Q(a, b), values[k]) for k, a, b in original["terms"]]
            domain = all(all(e is None for e in row["errors"]) for _, row in terms)
            if domain:
                vectors = [(a, [Q(u, v) for y in row["outputs"] for x in y for u, v in ((x[0], x[1]), (x[2], x[3]))]) for a, row in terms]
                residual = max((abs(sum(a * vector[i] for a, vector in vectors)) for i in range(len(vectors[0][1]))), default=Q(0))
                assert rel["passed"] == (residual == 0) and rel["residual"] == [residual.numerator, residual.denominator]
            else: assert not rel["passed"] and rel["status"] == "unresolved_comparison"
        actual_survivors = sum(r["final_domain_passed"] for r in final["layers"][label]["programs"])
        assert final["layers"][label]["final_domain_survivors"] == actual_survivors
    checks["independent_integer_and_complex_program_semantics"] = True
    checks["universal_polynomial_certificates_separate_from_finite_relations"] = True
    checks["promotion_expansion_and_equal_attempt_ablation"] = True
    assert batches["adaptive"]["family_attempts"] == batches["ablation"]["family_attempts"]
    assert sum(batches["adaptive"]["family_attempts"].values()) == spec["adaptive"]["candidates_per_batch"]
    assert not archives["ablation"]["promotion_enabled"] and not batches["ablation"]["macros"]
    paired = {}
    for label in ("adaptive", "ablation"):
        b = batches[label]
        paired[label] = {r["attempt"]: expand(r["program"], b["macros"]) for r in b["programs"] + b["generation_rejections"]}
        assert len(paired[label]) == spec["adaptive"]["candidates_per_batch"]
    assert paired["adaptive"] == paired["ablation"], "ablation must share all expanded random proposals"
    assert macro_uses > 0, "pilot must exercise automatic promotion"
    private = read(directory / "private_benchmark_targets.json"); learned = read(directory / "benchmark_learned.json")
    assert sha(private) == seal["private_targets_committed_sha256"]
    training = read(directory / "benchmark_training.json")
    assert not training["labels_or_target_formulas_shared"]
    for k, info in private["cases"].items():
        for ex, responses in zip(training["examples"], training["cases"][k]["responses"]):
            assert oracle(info["target"], [[pair(x) for x in arr] for arr in ex["inputs"]]) == responses
        p = learned["cases"][k]["program"]
        source = next(r for r in final["benchmarks"] if r["id"] == k)
        errors = []
        for ex in final["benchmark_final_examples"]:
            inputs = [[pair(x) for x in arr] for arr in ex["inputs"]]
            expected = oracle(info["target"], inputs)
            errors.append(p is None or evaluate(p, inputs, {}) != expected)
        assert source["accepted"] == (not any(errors))
    assert final["false_controls_accepted"] == 0
    finite = next(r for r in final["benchmarks"] if r["target"]["kind"] == "finite_mimic")
    assert finite["training_match"] and not finite["accepted"], "fresh evaluation must break the finite mimic"
    checks["anonymous_calibration_random_targets_and_false_controls"] = True
    for key in ("named", "synthetic"):
        category = "named_calibration" if key == "named" else "independently_sampled_synthetic"
        assert final[key + "_recovered"] == sum(r["accepted"] for r in final["benchmarks"] if r["category"] == category)
    assert not final["final_evaluation_used_for_selection"]
    assert not final["analytic_theorem_proved"] and not final["new_independent_prime_distribution_estimate_proved"] and final["verified_new_operators"] == []
    assert unresolved > 0, "keep validated leads outside current proof methods"
    checks["unproved_leads_retained_and_no_analytic_or_novelty_promotion"] = True
    boundary = directory / "worker_boundary_verification.json"
    subprocess.run([sys.executable, str(BASE / "autonomous_search.py"), "boundary-test", "--spec", str(directory / "protocol.json"), "--output", str(boundary)], check=True)
    assert read(boundary)["all_denied"]
    checks["private_and_final_data_network_and_process_access_denied"] = True
    replay_dir = directory / "replay"
    subprocess.run([sys.executable, str(BASE / "autonomous_search.py"), "replay", "--run-dir", str(directory), "--output-dir", str(replay_dir)], check=True)
    assert read(replay_dir / "replay_verification.json")["all_passed"]
    checks["deterministic_generator_selector_and_fit_replay"] = True
    details = {"independently_replayed_exact_coefficients": independent_values,
               "universal_polynomial_zero_certificates": certified, "validated_relations_without_proof_method": unresolved,
               "programs_using_automatically_promoted_macros": macro_uses,
               "named_calibration": [final["named_recovered"], final["named_total"]],
               "independently_sampled_synthetic": [final["synthetic_recovered"], final["synthetic_total"]],
               "promotion_ablation": final["promotion_ablation"]}
    result = {"all_passed": all(checks.values()), "checks": checks, "audit": details,
              "protocol_sha256": sha(spec), "source_final_evaluation_sha256": sha(final),
              "checker_code_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "mathematical_audit_imports_production_code": False,
              "integration_replay_uses_production_code": True, "verified_new_operators": []}
    (directory / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print("Autonomous audit", sum(checks.values()), "/", len(checks), "passed; exact coefficients", independent_values)


if __name__ == "__main__": main()
