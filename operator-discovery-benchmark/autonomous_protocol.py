"""Freeze a bounded independence pilot BEFORE generating response tables."""
from pathlib import Path
import hashlib
import json
import sys

from autonomous_grammar import VERSION, PRODUCTIONS, digest

BASE = Path(__file__).resolve().parent
CODE = ("autonomous_grammar.py", "autonomous_protocol.py", "autonomous_search.py",
        "autonomous_evaluation.py", "check_autonomous_search.py", "exact_arithmetic.py")


def specification():
    return {
        "schema": 1, "grammar_version": VERSION, "productions": PRODUCTIONS,
        "code_sha256": {name: hashlib.sha256((BASE / name).read_bytes()).hexdigest() for name in CODE},
        "baseline": {"index_leaves": ["n", "i", "N", 0, 1, 2, 3], "index_cost_max": 3,
                     "index_operations": ["ia", "is", "im", "iq", "ir"], "comparisons": ["eq", "le", "lt"],
                     "sequence_cost_max": 9, "inverse_sample_limit": 24, "inverse_sample_seed": 202610071,
                     "rule": "exhaustive cost-bounded scalar kernels and two-input predicates; finite inverse sample and polynomial seed templates separately declared"},
        "adaptive": {"seed": 202610072, "batches": 1, "candidates_per_batch": 192,
                     "encoded_cost_max": 16, "expanded_cost_max": 128,
                     "families": ["signed_sum", "point_product", "composition", "matrix_composition",
                                  "matrix_inverse", "bounded_sum", "nonlinear_norm", "index_mutation"],
                     "allocation": "identical expanded mutations in both arms; round robin equal attempts per family; rejected syntax retained"},
        "resources": {"operations_per_case": 2_000_000, "matrix_inverse_max_dimension": 128,
                      "archive_max": 40, "relation_dictionary_max": 36, "relation_max_terms": 3,
                      "relation_proposals_max": 48},
        "promotion": {"max_macros": 6, "minimum_reusing_programs": 2,
                      "minimum_expanded_cost": 3, "minimum_total_saving": 4,
                      "rule": "subtrees of validated programs, any declared type with explicit free indices; rank by reuse*(cost-1), then canonical hash; exact expansion retained"},
        "selection": {"criteria": ["short_description", "response_diversity", "validated_relation_membership", "empirical_prime_gain"],
                      "rule": "Pareto front plus equal round-robin criterion queues, exact behavioral deduplication; no final data",
                      "prime_baseline": "index residues modulo 2 and 3; output buckets zero, one, negative real, other",
                      "zero_oracle": False, "expected_formula_assertions": False},
        "data": {"discovery_seed": 202610073, "validation_seed": 202610074,
                 "discovery": [[6, "zeta_coefficients"], [9, "zeta_coefficients"], [8, "rational"], [5, "complex"]],
                 "validation": [[17, "zeta_coefficients"], [23, "zeta_coefficients"], [11, "rational"], [9, "complex"]],
                 "final": [[31, "rational"], [47, "complex"], [61, "zeta_coefficients"], [97, "zeta_coefficients"], [127, "sparse"]],
                 "final_seed_rule": "OS entropy, drawn by evaluator only AFTER archive and fitted benchmark programs are sealed",
                 "exact_tolerance": 0, "arithmetic": "Q and Q(i), exact; cancellation has no floating roundoff"},
        "calibration": {"dictionary_max": 160, "synthetic_targets": 2,
                        "target_seed_rule": "OS entropy in evaluator after protocol freeze; target choices/coefficients held until final evaluation",
                        "training_sizes": [4, 6], "final_sizes": [11, 19, 29],
                        "rule": "anonymous responses only; exhaustive one-feature scalar-kernel fits, stratified bounded two-feature fits; named calibrations and independently sampled in-language targets reported separately"},
        "boundaries": {"worker": "Python audit-hook read/write allowlist; deny network/process launches; enforcement prevents accidental leakage, not a hostile-code security sandbox",
                       "producer_prime_or_factor_queries": False, "prime_labels": "evaluator only; discovery summary metrics available to selector",
                       "adaptive_final_access": False, "literature_access": False, "model_calls": False},
        "assumptions": ["finite typed ASTs and supplied integer predicates restrict the search",
                        "scalar weights are rational; complex values arrive through generic inputs",
                        "finite matrix inverses have a declared dimension limit",
                        "small polynomial templates initialize nonlinear exploration",
                        "empirical prime contrast is not independent prime-distribution information",
                        "no analytic zeta/zero preservation primitive or convergence theorem is supplied",
                        "random synthetic targets are independently sampled within this language, not an external mathematical novelty benchmark"],
        "imported_proof_dependencies": ["commutative polynomial ring axioms", "exact_arithmetic.py (finite corroboration only)"],
    }


def validate_spec(s):
    if s["schema"] != 1 or s["grammar_version"] != VERSION:
        raise ValueError("unsupported protocol")
    for name, expected in s["code_sha256"].items():
        if hashlib.sha256((BASE / name).read_bytes()).hexdigest() != expected:
            raise ValueError("frozen code changed: " + name)
    if s["boundaries"]["adaptive_final_access"] or s["boundaries"]["producer_prime_or_factor_queries"]:
        raise ValueError("invalid independence boundary")


def freeze(path):
    path = Path(path)
    s = specification()
    if path.exists():
        old = json.loads(path.read_text()); validate_spec(old)
        if old != s: raise ValueError("protocol exists; use a new run directory")
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(s, indent=2) + "\n")
    return digest(s)


if __name__ == "__main__":
    print(freeze(sys.argv[1]))
