#!/usr/bin/env python3
"""Frozen baseline + rule-driven adaptive discovery; no nominated answer laws.

The coordinator launches restricted workers and a separate evaluator. Workers
only see allowlisted frozen batches and discovery/validation responses. Final
cases and private benchmark targets are generated/held by the evaluator.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction as Q
from itertools import product, combinations
import json
import math
import random
import socket  # preload before the worker guard; access is still denied
from pathlib import Path
import subprocess
import sys

import exact_arithmetic  # declared certificate backend, loaded before access guard
from autonomous_grammar import (canonical, cost, digest, expanded, infer, subterms,
                                polynomial_certificate)
from autonomous_protocol import freeze, validate_spec

BASE = Path(__file__).resolve().parent


def read(path): return json.loads(Path(path).read_text())


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")


def guard(readable, writable):
    """Prevent accidental access to evaluator/private data, network, other tools.

    No claim of protection against malicious native extensions or hostile code.
    All required modules are imported before installation; files are exact paths.
    """
    reads = {str(Path(p).resolve()) for p in readable if p}
    writes = {str(Path(p).resolve()) for p in writable if p}
    def audit(event, args):
        if event == "open":
            path, mode, flags = args
            if not isinstance(path, (str, bytes, Path)): raise PermissionError("descriptor open denied")
            key = str(Path(path).resolve())
            iswrite = bool(flags & 3 or flags & 0x40 or flags & 0x200)
            if key not in (writes if iswrite else reads):
                raise PermissionError("worker file access denied: " + key)
        if event.startswith("socket.") or event in {"subprocess.Popen", "os.system", "os.fork", "os.exec", "ctypes.dlopen"}:
            raise PermissionError("worker network/process/native access denied")
    sys.addaudithook(audit)
    return {"read_paths": sorted(reads), "write_paths": sorted(writes),
            "network": "denied", "subprocess": "denied", "model_and_literature": "unavailable"}


def variables(t):
    return {p[1] for p in subterms(t) if p[0] == "v"}


def free_indices(t, bound=frozenset()):
    if t[0] == "v": return {t[1]} - bound - {"N"}
    if t[0] in {"kernel", "tab"}:
        return free_indices(t[1], bound | ({"n", "i"} if t[0] == "kernel" else {"n"}))
    if t[0] == "pair":
        return free_indices(t[1], bound | {"n", "i", "j"}) | free_indices(t[2], bound) | free_indices(t[3], bound)
    if t[0] == "bsum": return free_indices(t[2], bound) | free_indices(t[3], bound | {t[1]})
    return set().union(*(free_indices(x, bound) for x in t[1:] if isinstance(x, list)))


def baseline(spec):
    s = spec["baseline"]; leaves = [["v", x] if isinstance(x, str) else ["int", x] for x in s["index_leaves"]]
    exprs = leaves + [[op, a, b] for op, a, b in product(s["index_operations"], leaves, leaves)]
    seqs = []; rejected = []; seen = set()
    def add(t, family, limit=None):
        key = digest(t)
        if key in seen: return
        seen.add(key)
        try:
            if infer(t) != "sequence": raise ValueError("wrong root type")
            if cost(t) > (s["sequence_cost_max"] if limit is None else limit): return
        except ValueError as e:
            rejected.append({"program": t, "reason": "static type: " + str(e)}); return
        seqs.append({"id": key, "program": t, "family": family, "encoded_cost": cost(t), "expanded_cost": cost(t)})
    for i in (0, 1): add(["input", i], "sequence_leaf")
    for q in (-2, -1, 0, 1, 2):
        add(["tab", ["q", q, 1]], "scalar_sequence")
        for i in (0, 1): add(["scale", ["q", q, 1], ["input", i]], "signed_weight")
    for a, b in product((0, 1), repeat=2):
        add(["point", ["input", a], ["input", b]], "nonlinear_product")
        add(["add", ["input", a], ["input", b]], "signed_sum")
    for i in (0, 1): add(["norm2", ["input", i]], "nonlinear_norm")
    kernels = []
    scalars = [["embed", e] for e in exprs]
    scalars += [["indicator", [op, a, b]] for op, a, b in product(s["comparisons"], exprs, exprs)
                if cost(a) + cost(b) <= 4]
    for x in scalars:
        v = variables(x)
        if "i" not in v: continue
        p = ["apply", ["kernel", x], ["input", 0]]
        before = len(seqs); add(p, "scalar_kernel")
        if len(seqs) > before: kernels.append(["kernel", x])
    # Exhaustive predicates of the same cost bound over all three indices.
    tri_leaves = [["v", x] for x in ("n", "i", "j")] + [["int", x] for x in (0, 1, 2, 3)]
    tri_exprs = tri_leaves + [[op, a, b] for op, a, b in product(s["index_operations"], tri_leaves, tri_leaves)]
    for op, a, b in product(s["comparisons"], tri_exprs, tri_exprs):
        if cost(a) + cost(b) > 4 or not {"n", "i", "j"} <= variables([op, a, b]): continue
        add(["pair", ["indicator", [op, a, b]], ["input", 0], ["input", 1]], "bilinear_predicate")
    rng = random.Random(s["inverse_sample_seed"])
    admissible = [k for k in kernels if cost(k) + 3 <= s["sequence_cost_max"] + 1]
    for k in rng.sample(admissible, min(len(admissible), s["inverse_sample_limit"])):
        add(["apply", ["minverse", k], ["input", 0]], "finite_matrix_inverse", s["sequence_cost_max"] + 1)
    seqs.sort(key=lambda r: (r["encoded_cost"], r["id"]))
    return {"mode": "fixed_baseline", "macros": {}, "programs": seqs, "generation_rejections": rejected,
            "family_counts": dict(Counter(r["family"] for r in seqs)), "protocol_sha256": digest(spec)}


def flatten(row):
    return [Q(a, b) for values in row["outputs"] for x in values for a, b in ((x[0], x[1]), (x[2], x[3]))]


def successful(row): return all(x is None for x in row["errors"])


def relation_fit(y, a, b):
    first = next((i for i, (x, z) in enumerate(zip(a, b)) if x or z), None)
    if first is None: return None
    second = next((i for i, (x, z) in enumerate(zip(a, b)) if a[first] * z - b[first] * x), None)
    if second is None: return None
    d = a[first] * b[second] - b[first] * a[second]
    u = (y[first] * b[second] - y[second] * b[first]) / d
    v = (a[first] * y[second] - a[second] * y[first]) / d
    if not u or not v or max(abs(u.numerator), abs(v.numerator), u.denominator, v.denominator) > 32: return None
    if any(z != u * x + v * w for z, x, w in zip(y, a, b)): return None
    conditioning = abs(d) / max(Q(1), abs(a[first]), abs(b[first]), abs(a[second]), abs(b[second])) ** 2
    return u, v, {"pivot_rows": [first, second], "determinant": [d.numerator, d.denominator],
                  "scaled_pivot_separation": float(conditioning), "acceptance_arithmetic": "exact"}


def propose(spec, batch, discovery):
    by_id = {r["id"]: r for r in batch["programs"]}
    groups = defaultdict(list)
    for r in discovery["records"]:
        if successful(r): groups[canonical(r["outputs"])].append(r["id"])
    relations = []
    for ids in groups.values():
        ids.sort(key=lambda k: (by_id[k]["encoded_cost"], k))
        if len(ids) > 1:
            relations.append({"terms": [[ids[0], 1, 1], [ids[1], -1, 1]],
                              "method": "exact response-kernel alias", "conditioning": "exact coefficient subtraction"})
    rows = {r["id"]: r for r in discovery["records"] if successful(r)}
    # Round robin over production families, then keep distinct nonzero vectors.
    queues = defaultdict(list)
    for r in batch["programs"]:
        if r["id"] in rows: queues[r["family"]].append(r["id"])
    dictionary = []; fingerprints = set()
    while queues and len(dictionary) < spec["resources"]["relation_dictionary_max"]:
        for family in sorted(list(queues)):
            k = queues[family].pop(0)
            if not queues[family]: del queues[family]
            fp = canonical(rows[k]["outputs"])
            if fp not in fingerprints and any(flatten(rows[k])):
                dictionary.append(k); fingerprints.add(fp)
    vecs = {k: flatten(rows[k]) for k in dictionary}
    for k in dictionary:
        for a, b in combinations((x for x in dictionary if x != k), 2):
            fit = relation_fit(vecs[k], vecs[a], vecs[b])
            if fit:
                u, v, condition = fit
                relations.append({"terms": [[k, 1, 1], [a, -u.numerator, u.denominator], [b, -v.numerator, v.denominator]],
                                  "method": "three-column exact sparse nullspace", "conditioning": condition})
                break
    for row in relations:
        row["id"] = digest(row)
        row["training_residual"] = 0
        row["feature_dictionary"] = dictionary if len(row["terms"]) > 2 else [x[0] for x in row["terms"]]
    relations.sort(key=lambda r: (sum(by_id[k]["encoded_cost"] for k, _, _ in r["terms"]), r["id"]))
    cap = spec["resources"]["relation_proposals_max"]
    return {"protocol_sha256": digest(spec), "batch_sha256": digest(batch), "relations": relations[:cap],
            "resource_rejected_relations": [{**r, "reason": "frozen relation-evaluation budget"} for r in relations[cap:]],
            "dictionary": dictionary, "dictionary_assumption": "supplied program response columns, at most three terms with small rational coefficients"}


def relation_program(rel, by_id):
    terms = [["scale", ["q", a, b], by_id[k]["program"]] for k, a, b in rel["terms"]]
    t = terms[0]
    for child in terms[1:]: t = ["add", t, child]
    return t


def promote(spec, archive, batch):
    bodies = {}; users = defaultdict(set)
    for r in archive:
        t = expanded(r["program"], batch["macros"])
        for p in subterms(t):
            if cost(p) < spec["promotion"]["minimum_expanded_cost"]: continue
            try:
                typename = infer(p, frozenset(free_indices(p)))
            except ValueError: continue
            key = digest(p); bodies[key] = p; users[key].add(r["id"])
    candidates = []
    for k, ids in users.items():
        saving = len(ids) * (cost(bodies[k]) - 1)
        if len(ids) >= spec["promotion"]["minimum_reusing_programs"] and saving >= spec["promotion"]["minimum_total_saving"]:
            candidates.append((saving, k, ids))
    out = {}
    for saving, k, ids in sorted(candidates, key=lambda r: (-r[0], r[1]))[:spec["promotion"]["max_macros"]]:
        out[k] = {"body": bodies[k], "type": infer(bodies[k], frozenset(free_indices(bodies[k]))),
                  "free_indices": sorted(free_indices(bodies[k])), "dependency_ids": [], "evidence_program_ids": sorted(ids),
                  "reusing_programs": len(ids), "total_encoded_saving": saving,
                  "semantic_status": "exact syntax expansion, valid on original declared domains",
                  "utility_status": "discovery-validation evidence; no new theorem asserted"}
    return out


def select(spec, batch, discovery, validation, proposals, promotion_enabled=True):
    by_id = {r["id"]: r for r in batch["programs"]}
    train = {r["id"]: r for r in discovery["records"]}; val = {r["id"]: r for r in validation["records"]}
    relations = []; membership = Counter()
    for rel in proposals["relations"]:
        domain = all(successful(val[k]) for k, _, _ in rel["terms"])
        terms = [(Q(a, b), flatten(val[k])) for k, a, b in rel["terms"]] if domain else []
        residual = max((abs(sum((a * v[i] for a, v in terms), Q(0))) for i in range(len(terms[0][1]))), default=Q(0)) if terms else None
        fits = domain and residual == 0
        p = relation_program(rel, by_id)
        cert = polynomial_certificate(p, batch["macros"]) if fits else {"status": "not_attempted", "imported_theorems": []}
        if cert.get("status") == "universal_arithmetic_identity_proved" and cert.get("normal_form"):
            cert = {"status": "counterexample_to_universal_zero_identity", "normal_form": cert["normal_form"], "imported_theorems": []}
        status = "counterexample_found" if domain and not fits else ("universal_arithmetic_theorem_proved" if cert["status"] == "universal_arithmetic_identity_proved" else ("finite_identity_verified" if fits else "unresolved_comparison"))
        relations.append({**rel, "program": p, "validation_residual": None if residual is None else [residual.numerator, residual.denominator],
                          "validation_passed": fits, "status": status, "certificate": cert,
                          "analytic_status": "not_audited", "historical_novelty": "not_audited"})
        if fits:
            membership.update(k for k, _, _ in rel["terms"])
    candidates = []; ledger = []; seen = {}
    for r in batch["programs"]:
        k = r["id"]
        if not successful(train[k]) or not successful(val[k]):
            ledger.append({"id": k, "selected": False, "reason": "declared-domain/singular/operation failure", "discovery_errors": train[k]["errors"], "validation_errors": val[k]["errors"]}); continue
        fp = digest([train[k]["outputs"], val[k]["outputs"]])
        if fp in seen:
            ledger.append({"id": k, "selected": False, "reason": "finite behavioral duplicate", "duplicate_of": seen[fp], "universal_equality_claimed": False}); continue
        seen[fp] = k
        flat = flatten(val[k]); distinct = len({tuple(x) for y in val[k]["outputs"] for x in y})
        gain = val[k]["prime_metrics"]["conditional_information_bits"]
        row = {**r, "status": "numerical_lead", "certificate_status": "not_attempted_for_program_property",
               "scores": {"short_description": -r["encoded_cost"], "response_diversity": distinct,
                          "validated_relation_membership": membership[k], "empirical_prime_gain": gain},
               "exact_across_generic_real_complex_and_scales": True, "behavior_fingerprint": fp,
               "empirical_prime_metrics": val[k]["prime_metrics"], "rh_audit": "ordinary-zeta bridge not supplied",
               "new_independent_prime_information_proved": False, "historical_novelty": "not_audited"}
        candidates.append(row)
    # Pareto membership is diagnostic, not an exclusive filter. The archive
    # reserves equal turns for four different criteria and retains unproved leads.
    criteria = spec["selection"]["criteria"]
    front = []
    for r in candidates:
        if not any(all(z["scores"][c] >= r["scores"][c] for c in criteria) and any(z["scores"][c] > r["scores"][c] for c in criteria) for z in candidates): front.append(r["id"])
    queues = {c: sorted(candidates, key=lambda r: (-r["scores"][c], r["encoded_cost"], r["id"])) for c in criteria}
    archive = []; chosen = set()
    while len(archive) < spec["resources"]["archive_max"] and any(queues.values()):
        for c in criteria:
            while queues[c] and queues[c][0]["id"] in chosen: queues[c].pop(0)
            if queues[c] and len(archive) < spec["resources"]["archive_max"]:
                r = queues[c].pop(0); archive.append({**r, "selection_criterion": c, "on_pareto_front": r["id"] in front}); chosen.add(r["id"])
    for r in candidates:
        ledger.append({"id": r["id"], "selected": r["id"] in chosen,
                       "reason": "multi-criterion archive" if r["id"] in chosen else "archive resource limit", "scores": r["scores"]})
    macros = promote(spec, archive, batch) if promotion_enabled else {}
    return {"protocol_sha256": digest(spec), "batch_sha256": digest(batch), "discovery_sha256": digest(discovery),
            "validation_sha256": digest(validation), "proposals_sha256": digest(proposals), "mode": batch["mode"],
            "archive": archive, "selection_ledger": ledger, "relations": relations, "promotions": macros,
            "pareto_front": front, "promotion_enabled": promotion_enabled,
            "final_data_used": False, "verified_new_operators": []}


def compress(t, macros):
    k = digest(t)
    if k in macros: return ["macro", k]
    return [t[0]] + [compress(x, macros) if isinstance(x, list) else x for x in t[1:]]


def substitute(t, replacement):
    if t == ["input", 0]: return replacement
    return [t[0]] + [substitute(x, replacement) if isinstance(x, list) else x for x in t[1:]]


def adaptive(spec, archive, enabled):
    s = spec["adaptive"]; rng = random.Random(s["seed"]); macros = archive["promotions"] if enabled else {}
    # Both arms generate identical expanded mutations. Only the encoding and
    # admission cost differ, so the ablation does not change random proposals.
    pool = [expanded(r["program"], {}) for r in archive["archive"]]
    maps = [p[1] for r in archive["archive"] for p in subterms(r["program"]) if p[0] == "apply" and p[1][0] == "kernel"]
    if not maps: maps = [["kernel", ["q", 1, 1]]]
    programs = []; rejected = []; seen = set()
    for j in range(s["candidates_per_batch"]):
        f = s["families"][j % len(s["families"])]; a, b = rng.choice(pool), rng.choice(pool)
        q = ["q", rng.choice([-3, -2, -1, 1, 2, 3]), rng.choice([1, 2, 3])]
        if f == "signed_sum": t = ["add", a, ["scale", q, b]]
        elif f == "point_product": t = ["point", a, b]
        elif f == "composition": t = substitute(a, b)
        elif f == "matrix_composition": t = ["apply", ["mcompose", rng.choice(maps), rng.choice(maps)], a]
        elif f == "matrix_inverse": t = ["apply", ["minverse", rng.choice(maps)], a]
        elif f == "bounded_sum":
            idx = [rng.choice(["iq", "ir", "im", "ia"]), ["v", "n"], ["v", "j"]]
            x = ["bsum", "j", ["v", "n"], ["indicator", [rng.choice(["eq", "le", "lt"]), idx, ["int", rng.randrange(4)]]]]
            t = ["point", ["tab", x], a]
        elif f == "nonlinear_norm": t = ["add", ["norm2", a], ["scale", q, b]]
        else:
            idx = [rng.choice(["iq", "ir", "im", "ia", "is"]), ["v", "n"], ["int", rng.randrange(1, 4)]]
            t = ["point", ["tab", ["embed", idx]], a]
        t = compress(t, macros)
        k = digest(t); ex = expanded(t, macros)
        reason = "duplicate generated syntax" if k in seen else ("encoded cost limit" if cost(t) > s["encoded_cost_max"] else ("expanded cost limit" if cost(ex) > s["expanded_cost_max"] else None))
        seen.add(k)
        try: infer(t, macros=macros)
        except ValueError as e: reason = "static type: " + str(e)
        if reason: rejected.append({"attempt": j, "family": f, "program": t, "reason": reason}); continue
        programs.append({"id": k, "program": t, "family": f, "attempt": j, "encoded_cost": cost(t), "expanded_cost": cost(ex)})
    return {"mode": "adaptive_promotion" if enabled else "adaptive_ablation_no_promotion", "macros": macros,
            "programs": programs, "generation_rejections": rejected,
            "family_counts": dict(Counter(r["family"] for r in programs)), "family_attempts": dict(Counter(s["families"][j % len(s["families"])] for j in range(s["candidates_per_batch"]))),
            "protocol_sha256": digest(spec), "parent_archive_sha256": digest(archive)}


def calibration_dictionary(spec, batch, *, bounded=True):
    # The evaluator chooses its random targets from this frozen, declared
    # dictionary, but owns its entropy, mixture coefficients and target labels.
    out = []; seen = set()
    for r in batch["programs"]:
        p = r["program"]
        if p[0] != "apply" or p[1][0] != "kernel": continue
        # Fingerprint independent of input values: exact small integer kernels.
        from autonomous_grammar import matrix, Budget
        try: M = matrix(p[1], 6, Budget(2_000_000), 128)
        except ValueError: continue
        fp = canonical([[str(x) for x in row] for row in M])
        if fp in seen or not any(x for row in M for x in row): continue
        seen.add(fp); out.append(r)
    if not bounded: return out
    # Explicit stratification by operation signature, not by target names.
    groups = defaultdict(list)
    for r in out:
        signature = tuple(sorted({p[0] for p in subterms(r["program"]) if p[0] in {"iq", "ir", "im", "ia", "is", "eq", "le", "lt"}}))
        groups[signature].append(r)
    chosen = []
    while groups and len(chosen) < spec["calibration"]["dictionary_max"]:
        for family in sorted(list(groups)):
            chosen.append(groups[family].pop(0))
            if not groups[family]: del groups[family]
            if len(chosen) == spec["calibration"]["dictionary_max"]: break
    return chosen


def fit_benchmarks(spec, batch, training):
    from autonomous_grammar import evaluate, decode, encode
    dictionary = calibration_dictionary(spec, batch, bounded=False)
    pair_dictionary = calibration_dictionary(spec, batch)
    examples = training["examples"]
    vectors = {}
    for r in dictionary:
        ys = [evaluate(r["program"], [[decode(x) for x in a] for a in ex["inputs"]])[0] for ex in examples]
        vectors[r["id"]] = [Q(a, b) for y in ys for x in y for a, b in ((encode(x)[0], encode(x)[1]), (encode(x)[2], encode(x)[3]))]
    cases = {}
    for k, info in training["cases"].items():
        y = [Q(a, b) for arr in info["responses"] for x in arr for a, b in ((x[0], x[1]), (x[2], x[3]))]
        matches = []
        for r in dictionary:
            v = vectors[r["id"]]; nz = next((i for i, x in enumerate(v) if x), None)
            if nz is not None:
                w = y[nz] / v[nz]
                if w and all(a == w * b for a, b in zip(y, v)):
                    matches.append(["scale", ["q", w.numerator, w.denominator], r["program"]])
        if not matches:
            for a, b in combinations(pair_dictionary, 2):
                fit = relation_fit(y, vectors[a["id"]], vectors[b["id"]])
                if fit:
                    u, v, _ = fit
                    matches.append(["add", ["scale", ["q", u.numerator, u.denominator], a["program"]], ["scale", ["q", v.numerator, v.denominator], b["program"]]])
                    break
        best = min(matches, key=lambda p: (cost(p), digest(p))) if matches else None
        cases[k] = {"program": best, "exact_training_match": best is not None, "complexity": cost(best) if best else None,
                    "expected_formula_used": False, "status": "finite_response_fit" if best else "unresolved_comparison"}
    return {"protocol_sha256": digest(spec), "training_sha256": digest(training), "dictionary_ids": [r["id"] for r in dictionary],
            "pair_dictionary_ids": [r["id"] for r in pair_dictionary],
            "feature_dictionary": "scalar-kernel programs, exact one/two-column rational fits", "cases": cases}


def run(directory):
    directory = Path(directory).resolve(); directory.mkdir(parents=True, exist_ok=True)
    if (directory / "seal.json").exists(): raise ValueError("sealed run exists; use --replay or a fresh output directory")
    protocol = directory / "protocol.json"; freeze(protocol)
    def command(script, *args): subprocess.run([sys.executable, str(BASE / script), *map(str, args)], cwd=BASE, check=True)
    def worker(mode, *args): command("autonomous_search.py", mode, "--spec", protocol, *args)
    batch = directory / "baseline_batch.json"; worker("baseline", "--output", batch)
    def discovery_stage(label, batch, enabled=True):
        d = directory / (label + "_discovery.json"); v = directory / (label + "_validation.json")
        rel = directory / (label + "_relations.json"); arc = directory / (label + "_archive.json")
        command("autonomous_evaluation.py", "collect", "--spec", protocol, "--batch", batch, "--split", "discovery", "--output", d)
        worker("propose", "--batch", batch, "--discovery", d, "--output", rel)
        command("autonomous_evaluation.py", "collect", "--spec", protocol, "--batch", batch, "--split", "validation", "--output", v)
        worker("select", "--batch", batch, "--discovery", d, "--validation", v, "--relations", rel, "--promotion", "on" if enabled else "off", "--output", arc)
        return arc
    baseline_arc = discovery_stage("baseline", batch)
    for enabled, label in [(True, "adaptive"), (False, "ablation")]:
        b = directory / (label + "_batch.json")
        worker("adaptive", "--archive", baseline_arc, "--promotion", "on" if enabled else "off", "--output", b)
        discovery_stage(label, b, enabled)
    training = directory / "benchmark_training.json"; private = directory / "private_benchmark_targets.json"
    command("autonomous_evaluation.py", "benchmark-create", "--spec", protocol, "--batch", batch, "--output", training, "--private", private)
    learned = directory / "benchmark_learned.json"
    worker("fit", "--batch", batch, "--training", training, "--output", learned)
    sealed_names = [p.name for p in sorted(directory.glob("*.json")) if not p.name.startswith("private_")]
    seal = {"protocol_sha256": digest(read(protocol)), "files": {n: digest(read(directory / n)) for n in sealed_names},
            "final_cases_created": False, "private_targets_committed_sha256": digest(read(private)), "selection_closed": True}
    write(directory / "seal.json", seal)
    command("autonomous_evaluation.py", "final", "--spec", protocol, "--run-dir", directory, "--output", directory / "final_evaluation.json")
    command("check_autonomous_search.py", "--run-dir", directory)


def replay(directory, output):
    directory = Path(directory).resolve(); output = Path(output).resolve(); output.mkdir(parents=True, exist_ok=True)
    spec = directory / "protocol.json"
    validate_spec(read(spec))
    def w(mode, name, **args):
        command = [sys.executable, str(BASE / "autonomous_search.py"), mode, "--spec", str(spec), "--output", str(output / name)]
        for k, v in args.items(): command += ["--" + k.replace("_", "-"), str(v)]
        subprocess.run(command, check=True, cwd=BASE)
        if read(output / name) != read(directory / name): raise ValueError("deterministic replay mismatch: " + name)
    w("baseline", "baseline_batch.json")
    for label in ("baseline", "adaptive", "ablation"):
        if label != "baseline":
            w("adaptive", label + "_batch.json", archive=output / "baseline_archive.json", promotion="on" if label == "adaptive" else "off")
        w("propose", label + "_relations.json", batch=output / (label + "_batch.json"), discovery=directory / (label + "_discovery.json"))
        w("select", label + "_archive.json", batch=output / (label + "_batch.json"), discovery=directory / (label + "_discovery.json"),
          validation=directory / (label + "_validation.json"), relations=output / (label + "_relations.json"), promotion="off" if label == "ablation" else "on")
    w("fit", "benchmark_learned.json", batch=output / "baseline_batch.json", training=directory / "benchmark_training.json")
    write(output / "replay_verification.json", {"all_passed": True, "matched_generated_batches_archives_and_anonymous_fits": 10,
                                               "final_data_used_by_workers": False, "source_seal_sha256": digest(read(directory / "seal.json"))})
    print("Deterministic replay passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["run", "replay", "baseline", "adaptive", "propose", "select", "fit", "boundary-test"])
    for k in ("spec", "output", "output-dir", "run-dir", "batch", "discovery", "validation", "relations", "archive", "training"):
        parser.add_argument("--" + k, type=Path)
    parser.add_argument("--promotion", choices=["on", "off"], default="on")
    args = parser.parse_args()
    if args.mode == "run": run(args.output_dir); return
    if args.mode == "replay": replay(args.run_dir, args.output_dir); return
    spec = read(args.spec); validate_spec(spec)
    files = [args.spec, args.batch, args.discovery, args.validation, args.relations, args.archive, args.training]
    guard_info = guard(files, [args.output])
    if args.mode == "boundary-test":
        denied = {}
        for name in ("private_benchmark_targets.json", "final_evaluation.json", "final_cases.json"):
            try: (args.spec.parent / name).read_text()
            except PermissionError: denied[name] = True
            else: denied[name] = False
        try: subprocess.run([sys.executable, "-c", "pass"])
        except PermissionError: denied["process_launch"] = True
        try: socket.socket()
        except PermissionError: denied["network_socket"] = True
        write(args.output, {"all_denied": all(denied.values()), "checks": denied, "guard": guard_info}); return
    if args.mode == "baseline": result = baseline(spec)
    elif args.mode == "adaptive": result = adaptive(spec, read(args.archive), args.promotion == "on")
    elif args.mode == "propose": result = propose(spec, read(args.batch), read(args.discovery))
    elif args.mode == "select": result = select(spec, read(args.batch), read(args.discovery), read(args.validation), read(args.relations), args.promotion == "on")
    else: result = fit_benchmarks(spec, read(args.batch), read(args.training))
    # Guard paths vary on replay; do not put them into deterministic content.
    result["worker_access_policy"] = "exact input/output allowlist, network/process launches denied"
    write(args.output, result)
    print(args.mode, args.output.name, "programs", len(result.get("programs", [])), "archive", len(result.get("archive", [])))


if __name__ == "__main__": main()
