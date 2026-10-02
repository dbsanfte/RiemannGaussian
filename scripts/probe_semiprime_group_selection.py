#!/usr/bin/env python3
"""Optional, public-input tournament over Suyama groups and cover scales.

Select the first certified factor on the smallest successful dyadic probe
scale in a fixed finite curve menu. This is not an oracle for globally
optimal elliptic curves and does not guarantee a useful curve exists.
All setup, smooth projection, failed probes and polynomial work are charged.
Reference factors and separate single-curve replays never enter selection.
"""
from __future__ import annotations

import argparse
import hashlib
import inspect
import json
import math
from pathlib import Path
import random
import runpy
import statistics
import time

ROOT = Path(__file__).resolve().parents[1]
ROUGH = runpy.run_path(str(ROOT / "scripts/probe_semiprime_rough_projection.py"))
LONG, SINGLE = ROUGH["LONG"], ROUGH["SINGLE"]

# Fixed before generation of the fresh corpus. Sigma=11 has classical
# enhanced torsion properties; those are a prior, not an input-wise oracle.
CURVES = (6, 11, 7, 8)
FIRST_WIDTH = 16
FRESH_SEED = 2026100281
HELDOUT_SEED = 2026100287
PILOT_CAP = 128
FAVOURED_CAP = 256

# The frozen baseline only exposes consecutive curves starting at six.
# Give its unchanged staged algorithm a starting-sigma parameter in an
# isolated function namespace, so the same curve menu can be compared.
# The exact one-line substitution is included in the saved provenance.
_BASELINE_SOURCE = inspect.getsource(LONG["curve_extract"])
assert _BASELINE_SOURCE.count("sigma = curve_index+6") == 1
_BASELINE_CODE = compile(_BASELINE_SOURCE.replace(
    "sigma = curve_index+6", "sigma = curve_index+curve_start"),
    "<frozen-staged-ECM-with-start-sigma>", "exec")


def existing_staged_family(n):
    """The old staged ECM, sequentially on precisely the same curve menu."""
    history = []
    for sigma in CURVES:
        namespace = dict(LONG["curve_extract"].__globals__)
        namespace["curve_start"] = sigma
        exec(_BASELINE_CODE, namespace)
        result = namespace["curve_extract"](n, max_curves=1, staged=True)
        history.append({"sigma": sigma, "status": result["status"]})
        if result["factor"]:
            return {**result, "family_history": history, "family_curves_used": len(history)}
    return {**result, "family_history": history, "family_curves_used": len(history)}


def scales(bound):
    """Dyadic widths, followed by the exact original cap if necessary."""
    width = min(FIRST_WIDTH, bound)
    out = [width]
    while width < bound:
        width = min(2 * width, bound)
        out.append(width)
    return out


class Counters:
    def __init__(self):
        self.data = dict.fromkeys((
            "doubles", "differential_adds", "scalar_bits",
            "coordinate_inversions", "coordinate_gcds", "projection_steps",
            "sieve_cells", "cover_width_sum", "baby_points", "giant_points",
            "convolutions", "packed_coefficients", "monic_reductions",
            "coherent_targets", "derivative_targets", "curves_initialized",
            "setup_inversions", "probes", "recovery_descents"), 0)

    def double(self, point, a24, n):
        self.data["doubles"] += 1
        return LONG["montgomery_double"](point, a24, n)

    def add(self, left, right, difference, n):
        self.data["differential_adds"] += 1
        return LONG["montgomery_add"](left, right, difference, n)

    def scale(self, point, k, a24, n):
        self.data["scalar_bits"] += k.bit_length()
        if k == 0:
            return 1, 0
        left, right = point, self.double(point, a24, n)
        for bit in bin(k)[3:]:
            if bit == "0":
                left, right = (self.double(left, a24, n),
                               self.add(left, right, point, n))
            else:
                left, right = (self.add(left, right, point, n),
                               self.double(right, a24, n))
        return left

    def progression(self, point, count, a24, n):
        out = []
        previous, current = (1, 0), point
        for index in range(count):
            out.append(current)
            following = (self.double(point, a24, n) if index == 0 else
                         self.add(current, point, previous, n))
            previous, current = current, following
        return out

    def coordinates(self, n, points):
        self.data["coordinate_gcds"] += len(points)
        coordinates, g = LONG["invert_coordinates"](n, points)
        if coordinates is not None:
            self.data["coordinate_inversions"] += 1
        return coordinates, g


def scalar_collision(n, roots, points, counters):
    """Deduplicate coherent roots and strip them using F', in one batch.

    Repeated shared roots cannot cause an uncharged quadratic recovery scan.
    All roots used in a recovery descent are globally distinct.
    """
    index = {}
    for i, root in enumerate(roots):
        index.setdefault(root, i)
    unique = list(index)
    batch = LONG["MonicBatch"](n)
    node = batch.tree(unique)
    values = batch.evaluate(node[0], points)
    shared = [point for point in points if point in index]
    derivative = [(i * coefficient) % n for i, coefficient in enumerate(node[0])][1:]
    derivative_values = dict(zip(shared, batch.evaluate(derivative, shared)))
    counters.data["coherent_targets"] += len(shared)
    counters.data["derivative_targets"] += len(shared)
    result = {"status": "no-collision", "factor": None}
    for j, (point, value) in enumerate(zip(points, values)):
        coherent = point in index
        g = math.gcd(derivative_values[point] if coherent else value, n)
        if g == n:
            counters.data["recovery_descents"] += 1
            g = (ROUGH["descend_without_global_root"](n, node, point) if coherent
                 else LONG["WEIGHTED"]["descend"](node, point, n))
        if g and 1 < g < n:
            for root in unique:
                signal = (point - root) % n
                if root != point and math.gcd(signal, n) == g:
                    result = {"status": "factor", "factor": g,
                              "baby_index": index[root], "giant_index": j,
                              "root": root, "point": point,
                              "certificate_signal": signal}
                    break
            if result["factor"] is None:
                # A derivative product can expose a proper divisor without
                # its first matching leaf having exactly the same GCD.
                result = {"status": "factor", "factor": g,
                          "certificate_signal": derivative_values[point]
                          if coherent else value, "giant_index": j}
            break
    for key, value in batch.stats().items():
        counters.data[key] += value
    return result


class Curve:
    def __init__(self, n, sigma, counters):
        self.n, self.sigma, self.counters = n, sigma, counters
        self.active, self.last_prime = True, 1
        self.initial = {"status": "ready", "factor": None}
        counters.data["curves_initialized"] += 1
        u, v = (sigma * sigma - 5) % n, (4 * sigma) % n
        x, z = pow(u, 3, n), pow(v, 3, n)
        denominator = 16 * x * v % n
        g = math.gcd(denominator, n)
        if g != 1:
            self.fail(g, "curve-setup", denominator)
            return
        counters.data["setup_inversions"] += 1
        self.a24 = pow(v - u, 3, n) * (3 * u + v) * pow(denominator, -1, n) % n
        discriminant = self.a24 * (self.a24 - 1) % n
        g = math.gcd(discriminant, n)
        if g != 1:
            self.fail(g, "singular-curve", discriminant)
            return
        self.point = (x, z)

    def fail(self, g, stage, signal):
        self.active = False
        self.initial = {"status": "factor" if 1 < g < self.n else "shared-collapse",
                        "factor": g if 1 < g < self.n else None,
                        "stage": stage, "certificate_signal": signal}

    def probe(self, width, powers):
        if not self.active:
            return self.initial.copy()
        n, c = self.n, self.counters
        c.data["probes"] += 1
        c.data["cover_width_sum"] += width
        for prime, exponent in powers:
            if prime <= self.last_prime:
                continue
            before = self.point
            self.point = c.scale(before, exponent, self.a24, n)
            self.last_prime = prime
            c.data["projection_steps"] += 1
            g = math.gcd(self.point[1], n)
            if g == n:
                # Unwind only this already-known prime power. All replay
                # work is charged. A shared first step remains explicit.
                trial, remaining = before, exponent
                while remaining > 1:
                    trial = c.scale(trial, prime, self.a24, n)
                    remaining //= prime
                    g = math.gcd(trial[1], n)
                    if g != 1:
                        self.point = trial
                        break
            if g != 1:
                self.fail(g, "curve-smooth", self.point[1])
                return self.initial.copy()
        baby = c.progression(self.point, width - 1, self.a24, n)
        step = c.scale(self.point, width, self.a24, n)
        c.data["baby_points"] += len(baby)
        roots, g = c.coordinates(n, baby)
        if g != 1:
            self.fail(g, "baby-coordinate", next(z for _, z in baby if math.gcd(z, n) != 1))
            return self.initial.copy()
        # Full target batches at each scale; total degree is soft-linear.
        giant = c.progression(step, width, self.a24, n)
        c.data["giant_points"] += len(giant)
        targets, g = c.coordinates(n, giant)
        if g != 1:
            self.fail(g, "giant-coordinate", next(z for _, z in giant if math.gcd(z, n) != 1))
            return self.initial.copy()
        result = scalar_collision(n, roots, targets, c)
        result["stage"] = "curve-cover"
        if result["factor"]:
            result.update({"projected_point": list(self.point), "a24": self.a24})
        return result


def run(n, curves=CURVES, adaptive=True, probe_ceiling=None, favoured_width=None):
    """Only N and public curve/scale parameters enter this algorithm."""
    if n < 4 or not curves or len(set(curves)) != len(curves):
        raise ValueError("N>=4 and a nonempty distinct curve menu required")
    if n % 2 == 0:
        return {"status": "factor", "factor": 2, "stage": "even"}
    root = math.isqrt(n)
    if root * root == n:
        return {"status": "factor", "factor": root, "stage": "square"}
    bound = SINGLE["ceil_root"](n, 6)
    # Safe for both unknown primes, not only the smaller one. Removing all
    # small prime powers also limits coherent short-order degeneracies.
    group_bound = n + 2 * root + 3
    counters, states, history = Counters(), {}, []
    ceiling = bound if probe_ceiling is None else min(bound, probe_ceiling)
    if ceiling < 2:
        raise ValueError("probe ceiling must be at least two")
    widths = scales(ceiling) if adaptive else [ceiling]
    if favoured_width is not None and ceiling < min(bound, favoured_width):
        widths.append(min(bound, favoured_width))
    for width in widths:
        counters.data["sieve_cells"] += width + 1
        powers = SINGLE["projection_powers"](width, group_bound)
        for sigma in ((curves[0],) if width > ceiling else curves):
            state = states.get(sigma)
            if state is None:
                state = states[sigma] = Curve(n, sigma, counters)
            if not state.active:
                result = state.initial.copy()
                if result["factor"] is None:
                    continue
            else:
                result = state.probe(width, powers)
            history.append({"sigma": sigma, "width": width,
                            "status": result["status"], "stage": result.get("stage")})
            if result["factor"]:
                factor = result["factor"]
                assert 1 < factor < n and n % factor == 0
                if "certificate_signal" in result:
                    assert math.gcd(n, result["certificate_signal"]) == factor
                return {**result, "algorithm": "adaptive-group-tournament" if adaptive
                        else "fixed-full-cover-family", "sigma": sigma,
                        "width": width, "bound": bound, "menu": list(curves),
                        "history": history, "cost": counters.data}
    return {"status": "group-budget-exhausted", "factor": None,
            "bound": bound, "menu": list(curves), "history": history,
            "cost": counters.data}


def run_hybrid(n):
    """A bounded pilot tournament, then the previous staged sigma=6 pass.

    The cap was selected on the exploratory corpus. It is frozen before
    the separate held-out corpus. Failed pilots and repeated fallback
    preparation are included in full-call timing, never offered for free.
    This preserves successful baseline inputs but is not globally optimal.
    """
    pilot = run(n, probe_ceiling=PILOT_CAP, favoured_width=FAVOURED_CAP)
    if pilot["factor"]:
        return {**pilot, "algorithm": "capped-group-pilot", "fallback_used": False}
    fallback = LONG["curve_extract"](n, max_curves=1, staged=True)
    if fallback["factor"]:
        assert 1 < fallback["factor"] < n and n % fallback["factor"] == 0
    return {**fallback, "algorithm": "capped-group-pilot", "fallback_used": True,
            "pilot_cost": pilot["cost"], "pilot_history": pilot["history"],
            "pilot_status": pilot["status"], "fallback_method": "existing-staged-sigma6"}


def validate():
    curves, recurrence, factors = 0, 0, 0
    for n in (35, 77, 143, 323, 2021, 49065649):
        for sigma in CURVES:
            c = Counters()
            state = Curve(n, sigma, c)
            if state.active:
                curves += 1
                for k in range(1, 24):
                    assert c.scale(state.point, k, state.a24, n) == LONG["montgomery_scale"](
                        state.point, k, state.a24, n)
                    recurrence += 1
        result = run(n)
        if result["factor"]:
            assert n % result["factor"] == 0
            factors += 1
    for bound in range(2, 1100):
        widths = scales(bound)
        assert widths[-1] == bound and sum(widths) < 4 * bound
        assert all(a < b <= 2 * a for a, b in zip(widths, widths[1:]))
    c = Counters()
    shared = scalar_collision(35, [3, 3, 8], [3], c)
    assert shared["factor"] == 5
    assert scalar_collision(35, [3, 3], [3] * 32, Counters())["factor"] is None
    return {"curve_setups_checked": curves, "scalar_recurrences_checked": recurrence,
            "proper_factors_checked": factors, "scale_schedules_checked": 1098,
            "shared_root_regressions": 2}


def corpus(seed=FRESH_SEED, include_regressions=True):
    # Public recovery never calls this reference-only sample generator.
    import sympy
    rng = random.Random(seed)
    rows = []
    for bits in (48, 64, 80):
        for _ in range(8):
            while True:
                p = int(sympy.nextprime(rng.randrange(1 << (bits // 2 - 1), 1 << (bits // 2))))
                q = int(sympy.nextprime(rng.randrange(1 << (bits // 2 - 1), 1 << (bits // 2))))
                n = p * q
                if p != q and p.bit_length() == q.bit_length() == bits // 2 and n.bit_length() == bits:
                    break
            rows.append({"class": "fresh-balanced", "bits": bits, "N_decimal": str(n),
                         "reference_factors_decimal": [str(p), str(q)]})
    if not include_regressions:
        return rows
    for n, p, q in ((49065649, 6827, 7187),
                    (8562316804979989201, 2346272483, 3649327547),
                    (477209897193541203289441, 661911275027, 720957498683),
                    (9710106156230271983, 2657477227, 3653881229),
                    (380307690410407004392769, 583031310739, 652293767771)):
        rows.append({"class": "saved-regression", "N_decimal": str(n),
                     "reference_factors_decimal": [str(p), str(q)]})
    return rows


def probe(repeats=3):
    rows = corpus()
    for row in rows:
        row["partition"] = "exploration"
    heldout = corpus(HELDOUT_SEED, include_regressions=False)
    for row in heldout:
        row["partition"] = "held-out"
    rows += heldout
    for row in rows:
        n = int(row["N_decimal"])
        tests = {"existing_staged_sigma6": (None, (6,)),
                 "existing_staged_family": ("legacy-family", CURVES),
                 "fixed_sigma6": (False, (6,)), "fixed_family": (False, CURVES),
                 "adaptive_sigma6": (True, (6,)), "adaptive_family": (True, CURVES),
                 "capped_pilot": ("hybrid", CURVES)}
        saved = {}
        timings = {name: [] for name in tests}
        # Rotate order to reduce systematic cache/scheduling effects. Still
        # a small shared-environment experiment, not a tuned ECM benchmark.
        names = list(tests)
        for repetition in range(repeats):
            for name in names[repetition % len(names):] + names[:repetition % len(names)]:
                adaptive, menu = tests[name]
                start = time.perf_counter()
                result = (LONG["curve_extract"](n, max_curves=1, staged=True)
                          if adaptive is None else existing_staged_family(n)
                          if adaptive == "legacy-family" else run_hybrid(n) if adaptive == "hybrid"
                          else run(n, menu, adaptive))
                timings[name].append(1000 * (time.perf_counter() - start))
                saved[name] = result
        row["tests"] = {name: {"result": saved[name], "median_ms": statistics.median(times),
                                "all_ms": times} for name, times in timings.items()}
        # Independent public-input replays define the best *probe scale*
        # in this finite menu. Never used to choose a group in run().
        singles = [run(n, (sigma,), True) for sigma in CURVES]
        successful = [r for r in singles if r["factor"]]
        best = min((r["width"] for r in successful), default=None)
        chosen = saved["adaptive_family"]
        assert chosen.get("width") == best or (best is None and chosen["factor"] is None)
        row["reference_only_best_probe"] = {"scope": "Independent public-input replay, not selector input.",
            "minimum_successful_width": best,
            "single_curve_results": [{"sigma": s, "width": r.get("width"), "factor": r["factor"],
                                      "status": r["status"]} for s, r in zip(CURVES, singles)]}
        print(json.dumps({"N": str(n), "chosen_sigma": chosen.get("sigma"),
                          "chosen_width": chosen.get("width"), "best_width": best,
                          "adaptive_ms": row["tests"]["adaptive_family"]["median_ms"]}), flush=True)
    sources = ("scripts/probe_semiprime_group_selection.py",
               "scripts/probe_semiprime_rough_projection.py",
               "scripts/probe_semiprime_long_period.py",
               "RiemannGaussian/SemiprimeGroupSelection.lean")
    return {"scope": "Finite-menu, minimum-probe-scale selection and measured speedups; no global optimum or universal one-sixth guarantee.",
            "curves": list(CURVES), "first_width": FIRST_WIDTH, "seed": FRESH_SEED,
            "heldout_seed": HELDOUT_SEED, "pilot_cap": PILOT_CAP,
            "favoured_cap": FAVOURED_CAP,
            "legacy_family_provenance": {"source_sha256": hashlib.sha256(_BASELINE_SOURCE.encode()).hexdigest(),
                "sole_algorithm_substitution": "sigma = curve_index+6 -> sigma = curve_index+curve_start",
                "scope": "Isolated function namespace; previous staged curve arithmetic, projection bound, target batches and recovery unchanged."},
            "timing_protocol": "Three full-call timings, rotating method order, warmed imports; all recovery setup/probes charged. Reference/sample/JSON cost excluded.",
            "checks": validate(), "rows": rows,
            "source_hashes": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest()
                              for p in sources if (ROOT / p).is_file()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("factor", "validate", "probe"))
    parser.add_argument("N", nargs="?", type=int)
    parser.add_argument("--curves", nargs="+", type=int, default=list(CURVES))
    parser.add_argument("--fixed", action="store_true")
    parser.add_argument("--hybrid", action="store_true")
    parser.add_argument("--repeats", type=int, default=3)
    parser.add_argument("--output", default="docs/semiprime-group-selection-audit.json")
    args = parser.parse_args()
    if args.command == "factor":
        if args.N is None:
            parser.error("factor requires N")
        output = (run_hybrid(args.N) if args.hybrid else
                  run(args.N, tuple(args.curves), not args.fixed))
    elif args.command == "validate":
        output = validate()
    else:
        if args.repeats < 1:
            parser.error("positive repeats required")
        output = probe(args.repeats)
        Path(args.output).write_text(json.dumps(LONG["safe_json"](output), indent=2) + "\n")
        print("saved", args.output)
        return
    print(json.dumps(LONG["safe_json"](output), indent=2))


if __name__ == "__main__":
    main()
