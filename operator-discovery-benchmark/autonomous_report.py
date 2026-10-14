#!/usr/bin/env python3
"""Publish only completed, independently checked independence-stage artifacts."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

BASE = Path(__file__).resolve().parent


def read(p): return json.loads(Path(p).read_text())


def sha(x):
    return hashlib.sha256(json.dumps(x, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()).hexdigest()


def summary(directory):
    directory = Path(directory).resolve()
    spec = read(directory / "protocol.json"); audit = read(directory / "verification.json")
    final = read(directory / "final_evaluation.json")
    if not audit["all_passed"] or not all(audit["checks"].values()): raise ValueError("independent audit incomplete")
    if audit["protocol_sha256"] != sha(spec) or audit["source_final_evaluation_sha256"] != sha(final): raise ValueError("audit dependency changed")
    seal = read(directory / "seal.json")
    if final["seal_sha256"] != sha(seal): raise ValueError("final seal changed")
    for name, expected in seal["files"].items():
        if sha(read(directory / name)) != expected: raise ValueError("sealed dependency changed: " + name)
    if sha(read(directory / "private_benchmark_targets.json")) != seal["private_targets_committed_sha256"]:
        raise ValueError("private target commitment changed")
    for name, expected in spec["code_sha256"].items():
        if hashlib.sha256((BASE / name).read_bytes()).hexdigest() != expected: raise ValueError("frozen code changed: " + name)
    counts = {}
    for label in ("baseline", "adaptive", "ablation"):
        b = read(directory / (label + "_batch.json")); a = read(directory / (label + "_archive.json"))
        counts[label] = {"generated_programs": len(b["programs"]), "generation_rejections": len(b["generation_rejections"]),
                         "families": b["family_counts"], "archive_size": len(a["archive"]), "automatic_promotions": len(a["promotions"]),
                         "relation_status_counts": dict(Counter(r["status"] for r in a["relations"])),
                         "final_relation_status_counts": dict(Counter(r["status"] for r in final["layers"][label]["relations"])),
                         "final_domain_survivors": final["layers"][label]["final_domain_survivors"]}
    behavior_sets = {}
    for label in ("adaptive", "ablation"):
        layer = final["layers"][label]
        good = {r["id"] for r in layer["programs"] if r["final_domain_passed"]}
        behavior_sets[label] = {sha(r["outputs"]) for r in layer["records"] if r["id"] in good}
    on, off = behavior_sets["adaptive"], behavior_sets["ablation"]
    comparison = {"shared_final_behaviors": len(on & off), "promotion_only_final_behaviors": len(on - off),
                  "ablation_only_final_behaviors": len(off - on), "net_final_behavior_count_change": len(on) - len(off),
                  "scope": "finite archived behaviors under paired proposals; admission gains alone do not establish better discovery"}
    return {"status": "bounded_independence_pilot_independently_verified", "run_directory": str(directory),
            "protocol_sha256": sha(spec), "verification_sha256": sha(audit), "final_evaluation_sha256": sha(final),
            "counts": counts, "audit": audit["audit"], "checks": audit["checks"],
            "named_calibration": [final["named_recovered"], final["named_total"]],
            "independently_sampled_synthetic": [final["synthetic_recovered"], final["synthetic_total"]],
            "false_controls_accepted": final["false_controls_accepted"], "promotion_ablation": final["promotion_ablation"],
            "archive_behavior_comparison": comparison,
            "assumptions": spec["assumptions"], "boundaries": spec["boundaries"],
            "ordinary_zeta_zero_bridge_proved": False, "new_independent_prime_distribution_estimate_proved": False,
            "historical_novelty_established": False, "verified_new_operators": []}


def publish(directory, latest=True):
    directory = Path(directory).resolve(); s = summary(directory)
    b, a, off = (s["counts"][x] for x in ("baseline", "adaptive", "ablation"))
    text = f"""DETECTOR INDEPENDENCE PILOT

Frozen protocol: {s['protocol_sha256']}
Baseline: {b['generated_programs']} typed programs; {b['archive_size']} selected across four declared criteria.
Adaptive: {a['generated_programs']} admitted programs; {a['generation_rejections']} rejected generation attempts.
Promotion-disabled ablation: {off['generated_programs']} admitted programs; {off['generation_rejections']} rejected attempts.
Both adaptive arms receive the same attempt allocation across eight production families.
Baseline automatic reusable productions: {b['automatic_promotions']}.
Named anonymous calibration recovery: {s['named_calibration'][0]}/{s['named_calibration'][1]}.
Independently randomized in-language target recovery: {s['independently_sampled_synthetic'][0]}/{s['independently_sampled_synthetic'][1]}.
Accepted false controls: {s['false_controls_accepted']}.
Independent checks: {sum(s['checks'].values())}/{len(s['checks'])}.

Generation and selection run without model calls, literature lookups, named
target labels or private/final-data access. Exact Q(i) removes roundoff from
these coefficient experiments. Final cases are drawn after sealing the archive.
All batches, inference dictionaries, fitted residuals, selection decisions,
rejected programs, promotion bodies and source dependencies are retained.
Worker file/network/process access restrictions prevent accidental leakage;
they are not a security sandbox against hostile native code.

The independently sampled targets use evaluator-owned OS entropy and a
separate scalar interpreter. They test recovery of unnamed combinations within
the declared language. This is not a blind benchmark of mathematical novelty.

Relations surviving validation include unsupported numerical leads, which
remain in the archive. Universal certificates are restricted to exact
commutative polynomial normalization, with the existing arithmetic backend
used as finite corroboration. Maps, bounded sums and conjugation are not
silently certified. Final domain/resource failure is distinct from a false law.

Promotion comparison (all values measured after selection closed):
{json.dumps(s['promotion_ablation'], indent=2)}

Archive comparison:
{json.dumps(s['archive_behavior_comparison'], indent=2)}
Operation totals above count successful evaluations; failed evaluations also
consume work. The fixed per-case caps and paired proposal budget are equal,
but these totals are not a comparison of total runtime or mathematical value.

Selection and relation status counts:
{json.dumps(s['counts'], indent=2)}

This pilot proves no new independent prime-distribution estimate, analytic
ordinary-zeta bridge, RH-strength bound or historical novelty. Finite successes
do not become all-scale estimates. Verified-new operator list remains empty.
Existing main-registry arithmetic and native-zeta counts are unchanged.

Every inspected final case is now spent evaluation evidence. Any later tuning
must freeze a new specification and draw a new evaluator-owned final seed.
"""
    (directory / "report.txt").write_text(text)
    (directory / "summary.json").write_text(json.dumps(s, indent=2) + "\n")
    if latest:
        (BASE / "autonomous-results/latest.json").write_text(json.dumps({"run_directory": str(directory), "summary_sha256": sha(s)}, indent=2) + "\n")
    return s


def load_latest():
    pointer = BASE / "autonomous-results/latest.json"
    if not pointer.exists(): return {"status": "not_run", "verified_new_operators": []}
    p = read(pointer); s = summary(p["run_directory"])
    if sha(s) != p["summary_sha256"]: raise ValueError("published independence-stage summary changed")
    return s


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__); p.add_argument("--run-dir", type=Path, required=True)
    p.add_argument("--no-latest", action="store_true"); a = p.parse_args()
    s = publish(a.run_dir, not a.no_latest)
    print("Published", s["run_directory"], "checks", len(s["checks"]))
