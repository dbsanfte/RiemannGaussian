#!/usr/bin/env python3
"""Native p-free binomial unit/carry probe, diagnostic only.

Exact integer and Gaussian-integer identities precede floating phase samples.
The extracted p-free unit never vanishes and is NOT the raw Lucas residue.
No source/asymptotic assertion is inferred from any finite sample.
"""
from __future__ import annotations

from math import comb, cos, sin, log, pi
from fractions import Fraction
from pathlib import Path
import json


def primes(limit: int) -> list[int]:
    return [n for n in range(3, limit + 1)
            if all(n % d for d in range(2, int(n ** 0.5) + 1))]


def vp(n: int, p: int) -> int:
    assert n > 0
    answer = 0
    while n % p == 0:
        n //= p
        answer += 1
    return answer


def unit(n: int, p: int) -> int:
    assert n > 0
    while n % p == 0:
        n //= p
    return n % p


def legendre(n: int, p: int) -> int:
    n %= p
    assert n != 0, "a p-free unit character must never vanish"
    return 1 if pow(n, (p - 1) // 2, p) == 1 else -1


def factorial_tables(limit: int, p: int) -> tuple[list[int], list[int]]:
    units, valuations = [1], [0]
    for n in range(1, limit + 1):
        units.append(units[-1] * unit(n, p) % p)
        valuations.append(valuations[-1] + vp(n, p))
    return units, valuations


def binomial_row(n: int, p: int) -> tuple[list[int], list[int], list[int]]:
    units, vals = factorial_tables(n, p)
    residues = [units[n] * pow(units[k] * units[n-k] % p, -1, p) % p
                for k in range(n + 1)]
    valuations = [vals[n] - vals[k] - vals[n-k] for k in range(n + 1)]
    return residues, valuations, [legendre(u, p) for u in residues]


def add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return a[0] + b[0], a[1] + b[1]


def mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]


def scale(a: tuple[int, int], s: int) -> tuple[int, int]:
    return a[0] * s, a[1] * s


def power(a: tuple[int, int], n: int) -> tuple[int, int]:
    answer = (1, 0)
    while n:
        if n & 1:
            answer = mul(answer, a)
        a = mul(a, a)
        n //= 2
    return answer


def trace(values: list[int], lam: tuple[int, int]) -> tuple[int, int]:
    result, lk = (0, 0), (1, 0)
    for a in values:
        result = add(result, scale(lk, a))
        lk = mul(lk, lam)
    return result


def analyse(p: int, q: int, r: int, s: int, counters: dict[str, int]) -> dict:
    P, Q = p ** r, q ** s
    D = P * Q
    up, vp_row, cp = binomial_row(D - 1, p)
    uq, vq_row, cq = binomial_row(D - 1, q)
    upp, vpp, cpp = binomial_row(Q - 1, p)
    uqq, vqq, cqq = binomial_row(P - 1, q)
    sp, sq = legendre(p - 1, p), legendre(q - 1, q)
    sigma = sp * sq
    values = [a * b for a, b in zip(cp, cq)]
    assert cp[0] == cp[-1] == cq[0] == cq[-1] == 1
    for k in range(D):
        # Depth reduction keeps the genuine p-free upper column and its carries.
        assert up[k] == ((-1) ** (k % P) * upp[k // P]) % p
        assert uq[k] == ((-1) ** (k % Q) * uqq[k // Q]) % q
        assert vp_row[k] == vpp[k // P]
        assert vq_row[k] == vqq[k // Q]
        assert values[k] == values[D - 1 - k]
        counters["exact_depth_reductions"] += 2
        counters["exact_valuation_reductions"] += 2
        counters["swapped_endpoint_reflections"] += 1
        if D <= 400:
            literal = comb(D - 1, k)
            assert up[k] == unit(literal, p)
            assert uq[k] == unit(literal, q)
            assert vp_row[k] == vp(literal, p)
            assert vq_row[k] == vp(literal, q)
            counters["direct_integer_binomial_checks"] += 1
    jump_p, jump_q = [], []
    for k in range(D - 1):
        t = k + 1
        # Exact quotient after extracting ALL p/q powers, not raw residue division.
        rp = legendre(unit(D - t, p) * pow(unit(t, p), -1, p), p)
        rq = legendre(unit(D - t, q) * pow(unit(t, q), -1, q), q)
        assert cp[k + 1] == rp * cp[k]
        assert cq[k + 1] == rq * cq[k]
        counters["exact_pfree_adjacent_recurrences"] += 2
        if t % P:
            assert rp == sp
            counters["depth_suppressed_p_crossings"] += int(t % p == 0)
        if t % Q:
            assert rq == sq
            counters["depth_suppressed_q_crossings"] += int(t % q == 0)
        if t % P == 0:
            assert t % Q != 0
            defect = sq * cq[k] * (cp[k + 1] - sp * cp[k])
            assert defect == values[k + 1] - sigma * values[k]
            jump_p.append((t, defect))
        elif t % Q == 0:
            defect = sp * cp[k] * (cq[k + 1] - sq * cq[k])
            assert defect == values[k + 1] - sigma * values[k]
            jump_q.append((t, defect))
        else:
            assert values[k + 1] == sigma * values[k]
    exact_codes = []
    for lam in ((1, 0), (-1, 0), (0, 1), (0, -1)):
        coded = trace(values, lam)
        endpoint = add((1, 0), scale(power(lam, D), -sigma))
        jp = (0, 0)
        jq = (0, 0)
        for t, d in jump_p:
            jp = add(jp, scale(power(lam, t), d))
        for t, d in jump_q:
            jq = add(jq, scale(power(lam, t), d))
        gap = add((1, 0), scale(lam, -sigma))
        assert mul(gap, coded) == add(endpoint, add(jp, jq))
        counters["exact_joined_jump_Fourier_identities"] += 1
        gap_sq = gap[0] ** 2 + gap[1] ** 2
        if gap_sq:
            assert gap_sq * (coded[0] ** 2 + coded[1] ** 2) <= (2 + 2 * P + 2 * Q) ** 2
            counters["exact_depth_gap_squared_bounds"] += 1
        if gap == (0, 0):
            # At resonance this is an exact derivative conservation law, NOT trace cancellation.
            assert add(endpoint, add(jp, jq)) == (0, 0)
            if D % 2:
                assert endpoint == (0, 0)
                assert add(jp, jq) == (0, 0)
                counters["odd_resonant_zero_jump_conservations"] += 1
            else:
                assert endpoint == (1 - sigma, 0)
                assert add(jp, jq) == (sigma - 1, 0)
                counters["even_resonant_endpoint_conservations"] += 1
            counters["exact_resonant_jump_conservations"] += 1
        exact_codes.append({"lambda": lam, "gap": gap, "trace": coded,
                            "endpoint": endpoint, "p_jump": jp, "q_jump": jq})
    if p == 2 and r == 1:
        # A genuinely source-sized native row, but its surviving code is only a
        # fixed residue-class selector: no cross-prime/depth coupling remains.
        assert values == [sq ** (k % Q) for k in range(D)]
        assert sum(values) == (D if sq == 1 else 2)
        assert trace(values, (-1, 0)) == (0, 0)
        counters["exact_fixed_cofactor_two_collapse_checks"] += 1
    # Exact coded resonance can be computed as a staircase overlap of upper columns.
    resonant_values = [sp ** (k // P) * cpp[k // P] *
                       sq ** (k // Q) * cqq[k // Q] for k in range(D)]
    assert sum(resonant_values) == trace(values, (sigma, 0))[0]
    counters["exact_resonant_staircase_identities"] += 1
    # Join both native upper-column incidences through their literal interval overlaps.
    ai = [sp ** i * cpp[i] for i in range(Q)]
    bj = [sq ** j * cqq[j] for j in range(P)]
    staircase_total = 0
    i, j = 0, 0
    edges = 0
    while i < Q and j < P:
        end = min((i + 1) * P, (j + 1) * Q)
        start = max(i * P, j * Q)
        width = end - start
        assert width > 0
        staircase_total += width * ai[i] * bj[j]
        edges += 1
        if (i + 1) * P == end:
            i += 1
        if (j + 1) * Q == end:
            j += 1
    assert edges == P + Q - 1
    assert staircase_total == sum(resonant_values)
    counters["exact_native_overlap_transport_identities"] += 1
    layers: dict[tuple[int, int], list[int]] = {}
    raw_values = []
    for k, a in enumerate(values):
        raw = a if vp_row[k] == vq_row[k] == 0 else 0
        raw_values.append(raw)
        key = (vp_row[k], vq_row[k])
        if key not in layers:
            layers[key] = [0, 0, 0]
        layers[key][0] += 1
        layers[key][1] += a
        layers[key][2] += sigma ** k * a
    assert sum(layer[2] for layer in layers.values()) == sum(resonant_values)
    raw_resonant = trace(raw_values, (sigma, 0))[0]
    raw_zero_carry_contribution = sum(layer[2] for key, layer in layers.items() if key != (0, 0))
    assert raw_resonant + raw_zero_carry_contribution == sum(resonant_values)
    # Floating EXTERNAL prime phases do not certify a source or asymptotic rate.
    floating = []
    for theta in (0.0, pi, 1 / D, 1 / P, 1 / Q):
        lam = complex(cos(theta), sin(theta))
        v = sum(a * lam ** k for k, a in enumerate(values)) / D
        floating.append({"theta": theta, "trace_real": v.real,
                         "trace_imag": v.imag, "trace_abs": abs(v),
                         "actual_gap": abs(1 - sigma * lam)})
    return {"p": p, "q": q, "r": r, "s": s, "P": P, "Q": Q, "D": D,
            "character_parities": [sp, sq], "sigma": sigma,
            "raw_zero_cells": sum(a > 0 or b > 0 for a, b in zip(vp_row, vq_row)),
            "unit_zero_cells": 0,
            "raw_resonant_trace": raw_resonant,
            "unit_only_carry_layer_resonant_trace": raw_zero_carry_contribution,
            "exact_valuation_layer_contributions": [
                {"vp": key[0], "vq": key[1], "population": layer[0],
                 "uncoded_unit_trace": layer[1], "resonant_unit_trace": layer[2]}
                for key, layer in sorted(layers.items())],
            "actual_p_jump_count": len(jump_p), "actual_q_jump_count": len(jump_q),
            "resonant_trace": sum(resonant_values),
            "exact_resonant_trace_normalized": [Fraction(sum(resonant_values), D).numerator,
                                                Fraction(sum(resonant_values), D).denominator],
            "resonant_trace_normalized": sum(resonant_values) / D,
            "exact_Gaussian_integer_codes": exact_codes,
            "floating_internal_codes_not_certificates": floating}


def main() -> None:
    counters = {k: 0 for k in (
        "native_rows", "proper_power_rows", "exact_depth_reductions",
        "exact_valuation_reductions", "swapped_endpoint_reflections",
        "direct_integer_binomial_checks", "exact_pfree_adjacent_recurrences",
        "depth_suppressed_p_crossings", "depth_suppressed_q_crossings",
        "exact_joined_jump_Fourier_identities", "exact_resonant_jump_conservations",
        "odd_resonant_zero_jump_conservations", "even_resonant_endpoint_conservations",
        "exact_resonant_staircase_identities", "exact_native_overlap_transport_identities",
        "exact_fixed_cofactor_two_collapse_checks", "exact_depth_gap_squared_bounds")}
    rows = [(p, q, r, s) for p in primes(31) for q in primes(31) if p < q
            for r in range(1, 4) for s in range(1, 4)
            if p ** r * q ** s <= 12000]
    rows += [(3, q, 1, 1) for q in primes(499) if q > 31]
    rows += [(p, q, 1, 1) for p, q in ((43, 47), (71, 73), (97, 101),
                                      (103, 107), (109, 113))]
    rows += [(2, q, r, s) for q in primes(31) for r in range(1, 5)
             for s in range(1, 4) if 2 ** r * q ** s <= 12000]
    examples = []
    for p, q, r, s in rows:
        examples.append(analyse(p, q, r, s, counters))
        counters["native_rows"] += 1
        counters["proper_power_rows"] += int(r + s > 2)
    output = {
        "scope": "genuine p-free binomial units with valuation/depth kept separately",
        "exact_integer_and_Gaussian_integer_checks": counters,
        "exact_identity_preflight": {
            "depth": "unit_p binom(PQ-1,k)=(-1)^(k mod P)*unit_p binom(Q-1,floor(k/P)) mod p",
            "valuation": "v_p binom(PQ-1,k)=v_p binom(Q-1,floor(k/P))",
            "recurrence": "ordinary ratio is sigma except P|k+1 or Q|k+1; BOTH depth jumps retained",
            "resonance": "at lambda=sigma, endpoint+joined jump sum is exactly0; oddD gives jump sum0, evenD gives jump sum sigma-1; coded mean is not constrained",
            "mean": "resonant trace equals staircase overlap of the two genuine upper unit columns",
            "overlap_transport": "S=sum_ij |[iP,(i+1)P) intersect [jQ,(j+1)Q)| A_i B_j, with P+Q-1 positive incidences",
            "arbitrary_array_gate": "the same overlap transport permits A_i=B_j=1 and trace D; geometry alone has no resonant saving",
            "same_prime_diagonal": "for two identical p-free character columns their product is exactly1 at every k, even in positive-valuation cells",
            "fixed_cofactor_two": "P=2 gives literal row chi_q(-1)^(k modQ); uncoded trace/D is1 onq=1mod4 and1/Q onq=3mod4; lambda=-1 trace0 always",
        },
        "paper_level_source_gate": {
            "native_code_source": "OPEN: no matched-zero Euler/Mellin response proved for growing unaligned unit staircase",
            "fixed_p": "finite row cancellation is not a growing-prime rate; fixed-p jump density remains nonshrinking",
            "prime_height": "external p^(-iy),q^(-iy) multiplies these exact finite rows but no source limit follows",
            "collapse": "after row join the outer packet is a prime sum weighted by its scalar staircase trace; no new independent arithmetic inequality supplied",
            "fixed_two_source_preflight": "uncoded main indicator(q=1mod4)=(1+chi4(q))/2; expected principal zeta residue and possible chi4-L residue have same negative sign; no proven source theorem in this numerical script",
            "fixed_two_collapse": "genuine fixed-cofactor-two residue-class selector has no remaining carry coupling; 1/Q correction lies in a safer absolute half-plane; requires separate exact analytic proof",
            "not_inferred": ["RH estimate", "actual hypothetical-zero source", "summed proper-power payment",
                             "asymptotic resonant decay", "complete p-free Euler series"]},
        "rows": examples,
        "all_probes_diagnostic_only": True,
    }
    fixed = [a for a in examples if a["p"] == 3 and a["r"] == a["s"] == 1]
    witnesses = []
    for level in (8, 12, 24, 72):
        witness = next(((a, b) for a in fixed for b in fixed
                        if a["q"] < b["q"] and a["q"] % level == b["q"] % level
                        and a["resonant_trace"] * b["resonant_trace"] < 0), None)
        if witness is not None:
            a, b = witness
            witnesses.append({"tested_level_only": level,
                              "same_q_residue": a["q"] % level,
                              "q1": a["q"], "q2": b["q"],
                              "unit_resonant_trace1": a["resonant_trace"],
                              "unit_resonant_trace2": b["resonant_trace"],
                              "scope": "exact finite witness excludes this fixed-residue scalar code only; NOT all finite character levels"})
    output["exact_fixed_p_residue_class_diagnostics"] = witnesses
    indexed = {a["q"]: a for a in fixed}
    if all(q in indexed for q in (5, 29, 53)):
        ss = [indexed[q]["resonant_trace"] for q in (5, 29, 53)]
        determinant = (29 - 5) * (ss[2] - ss[0]) - (53 - 5) * (ss[1] - ss[0])
        assert determinant != 0
        output["exact_old_bulk_endpoint_class_counterexample"] = {
            "tested_residue_level_only": 24, "primes": [5, 29, 53],
            "same_residue": 5, "unnormalized_unit_traces": ss,
            "affine_q_determinant": determinant,
            "scope": "excludes S(q)=a_r*q+b_r on this class, hence normalized periodic-bulk plus periodic-endpoint/q at level24 only"}
    target = Path(".lake/arithmetic-operator-pfree-structure")
    target.mkdir(parents=True, exist_ok=True)
    (target / "probe.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(counters, sort_keys=True))
    extremes = sorted(examples, key=lambda a: abs(a["resonant_trace_normalized"]), reverse=True)[:12]
    print(json.dumps([{k: a[k] for k in ("p", "q", "r", "s", "D", "sigma", "resonant_trace", "resonant_trace_normalized")}
                      for a in extremes], indent=2))


if __name__ == "__main__":
    main()
