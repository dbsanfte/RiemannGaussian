#!/usr/bin/env python3
"""One exact source preflight for fixed p=2 valuation-marked unit rows.

No source theorem is inferred from the finite digital identities. In particular
raw binomial residues and p-free units are never interchanged.
"""
from __future__ import annotations

from math import comb
from fractions import Fraction
from pathlib import Path
import json


def primes(n: int) -> list[int]:
    return [p for p in range(3, n + 1)
            if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def vp(n: int, p: int) -> int:
    assert n > 0
    r = 0
    while n % p == 0:
        n //= p
        r += 1
    return r


def unit(n: int, p: int) -> int:
    while n % p == 0:
        n //= p
    return n % p


def valuation_factorial(n: int) -> int:
    ans = 0
    while n:
        n //= 2
        ans += n
    return ans


def val_binom(n: int, k: int) -> int:
    return k.bit_count() + (n - k).bit_count() - n.bit_count()


def thue_convolution(n: int, cache: dict[int, int]) -> int:
    if n not in cache:
        if n % 2:
            cache[n] = -2 * thue_convolution(n // 2, cache)
        else:
            cache[n] = (thue_convolution(n // 2, cache) +
                        thue_convolution(n // 2 - 1, cache))
    return cache[n]


def main() -> None:
    counters = {k: 0 for k in ("native_rows", "proper_power_rows", "valuation_depth_checks",
                               "linear_midpoint_or_mean_identities", "parity_midpoint_or_mean_identities",
                               "direct_integer_unit_checks", "Thue_Morse_convolution_identities",
                               "exact_linear_factorial_identities", "exact_dyadic_suffix_identities")}
    rows = [(q, s) for q in primes(997) for s in range(1, 4) if q ** s <= 20000]
    rows += [(65537, 1)]
    cache = {-1: 0, 0: 1}
    examples = []
    for q, s in rows:
        Q, D = q ** s, 2 * q ** s
        sq = 1 if q % 4 == 1 else -1
        v = [val_binom(D - 1, k) for k in range(D)]
        a = [sq ** (k % Q) for k in range(D)]
        for k in range(D):
            assert v[k] == val_binom(Q - 1, k // 2)
            assert v[k] == v[D - 1 - k]
            assert a[k] == a[D - 1 - k]
            counters["valuation_depth_checks"] += 1
            if D <= 300:
                b = comb(D - 1, k)
                assert v[k] == vp(b, 2)
                uq = unit(b, q)
                char = 1 if pow(uq, (q - 1) // 2, q) == 1 else -1
                assert char == a[k]
                counters["direct_integer_unit_checks"] += 1
        linear = sum(x * y for x, y in zip(a, v))
        parity = sum(x * (-1) ** y for x, y in zip(a, v))
        midpoint = (Q - 1) // 2
        linear_upper = sum(val_binom(Q - 1, i) for i in range(Q))
        parity_upper = sum((-1) ** val_binom(Q - 1, i) for i in range(Q))
        factorial_expression = (Q * valuation_factorial(Q - 1) -
                                2 * sum(valuation_factorial(i) for i in range(Q)))
        digit_expression = 2 * sum(i.bit_count() for i in range(Q)) - Q * (Q - 1).bit_count()
        assert linear_upper == factorial_expression == digit_expression
        counters["exact_linear_factorial_identities"] += 1
        d, dyadic_suffix = 2, 0
        while d <= Q:
            dyadic_suffix += (Q // d) * (d - Q % d)
            d *= 2
        assert linear_upper == dyadic_suffix
        counters["exact_dyadic_suffix_identities"] += 1
        if sq == 1:
            assert linear == 2 * linear_upper
            assert parity == 2 * parity_upper
        else:
            # Both entries in the unique crossing pair have positive sign;
            # all the other even/odd pairs cancel BEFORE any norm.
            assert linear == 2 * midpoint.bit_count()
            assert parity == 2 * (-1) ** midpoint.bit_count()
        counters["linear_midpoint_or_mean_identities"] += 1
        counters["parity_midpoint_or_mean_identities"] += 1
        c = thue_convolution(Q - 1, cache)
        assert parity_upper == (-1) ** (Q - 1).bit_count() * c
        counters["Thue_Morse_convolution_identities"] += 1
        counters["native_rows"] += 1
        counters["proper_power_rows"] += int(s > 1)
        examples.append({"q": q, "s": s, "Q": Q, "q_character_parity": sq,
                         "unmarked_unit_sum": sum(a), "linear_marked_sum": linear,
                         "parity_marked_sum": parity,
                         "exact_linear_normalized": [Fraction(linear, D).numerator, Fraction(linear, D).denominator],
                         "exact_parity_normalized": [Fraction(parity, D).numerator, Fraction(parity, D).denominator],
                         "linear_upper_mean_sum": linear_upper,
                         "parity_upper_mean_sum": parity_upper,
                         "q_phase": "the full scalar q^(-iy) multiplies every exact identity; no substitution by a toy phase"})
    fermat_examples = []
    for h in (2, 4, 8, 16):
        Q = 2 ** h + 1
        e = next(row for row in examples if row["Q"] == Q and row["s"] == 1)
        assert e["linear_marked_sum"] == 2 * ((h - 1) * 2 ** h + 1)
        assert e["parity_marked_sum"] == 2 * ((5 + (-2) ** h) // 3)
        fermat_examples.append(e)
    out = {"all_probes_diagnostic_only": True,
           "exact_integer_checks": counters,
           "source_preflight": {
               "literal_q_phase": "retained multiplicatively, no phase freezing",
               "q_3_mod_4": "pairing reduces both marks to a midpoint; normalized weights O(log Q/Q) and O(1/Q)",
               "linear_q_1_mod_4": "exact factorial-valuation linear functional / dyadic suffix scalar; ordinary Archimedean Gamma identity requires summing ALL prime bases and does not identify this fixed-base mark",
               "nonlinear_q_1_mod_4": "exact Thue-Morse convolution coefficient at Q-1; genuinely digital, not the unmarked residue-class selector",
               "missing_actual_source_gate": "no exact Euler/logarithmic-derivative identity or actual matched-zero Mellin residue is established for either growing-depth digital weight on ordinary prime q",
               "finite_digit_expansion_is_not_enough": "finite periodic approximations do not control the growing binary depth or preserve the source-scale masked phase",
               "not_inferred": ["actual zero-mode response", "pole separation preserving that response", "cofinal decay or growth", "independent RH estimate"]},
           "exact_finite_fermat_prime_examples_not_asymptotics": fermat_examples,
           "rows": examples}
    path = Path(".lake/arithmetic-operator-pfree-marked")
    path.mkdir(parents=True, exist_ok=True)
    (path / "probe.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(counters, sort_keys=True))
    print(json.dumps([{k: e[k] for k in ("q", "linear_marked_sum", "parity_marked_sum", "exact_linear_normalized", "exact_parity_normalized")}
                      for e in fermat_examples], indent=2))


if __name__ == "__main__":
    main()
