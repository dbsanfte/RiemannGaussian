#!/usr/bin/env python3
"""Optional finite arithmetic regression for the reflected-prefix floor.

Every coordinate is an actual distinct prime. The cutoff uses the exact
integer floor in length, and the Riesz response is evaluated by enumerating
ALL squarefree divisors. These are individual labels, NOT a prime-density
model, a proof of coreBand membership, or a cofinal floor certificate.
Run outside CI with ../.venv/bin/python.
"""
import json
import math

import mpmath as mp
from scipy.stats import binom
from sympy import nextprime


def riesz(cutoff, logs):
    return mp.fsum(
        (-1) ** mask.bit_count()
        * max(mp.mpf(0), cutoff - mp.fsum(x for i, x in enumerate(logs) if mask >> i & 1))
        for mask in range(1 << len(logs))
    )


def row(N, shares, height=54):
    primes = []
    for share in shares:
        p = int(nextprime(int(mp.exp(mp.mpf(share) * (2 * N)))))
        while p in primes:
            p = int(nextprime(p))
        primes.append(p)
    logs = [mp.log(p) for p in primes]
    T = mp.fsum(logs)
    X = (20000**N // (10001**N * (N + 1)) + 2) ** 2
    L = mp.log(X)
    D = T - L
    outer = [x for x in logs if x >= D]
    active = [x for x in logs if x < D]
    v = L - mp.fsum(outer)
    secondary = [x for x in active if x < v]
    prefix = max(mp.mpf(0), v) - mp.fsum(max(mp.mpf(0), v - x) for x in active)
    direct = -T / L * riesz(L, logs)
    reflected = -T / L * (-1) ** len(outer) * riesz(v, active)
    primary_zero = len(active) >= 2 and mp.fsum(active) <= D
    secondary_zero = len(active) >= 2 and len(secondary) >= 2 and mp.fsum(secondary) <= v
    prefix_valid = len(outer) == 2 and len(logs) >= 4 and v / 2 <= min(active)
    phase = mp.cos(height * T)
    count = len(logs)

    def capacity(parity):
        return max(math.comb(count - 2, j) for j in range(count - 1) if j % 2 == parity)

    old_cost = T / L * T / count * (
        capacity(0) * max(phase, 0) + capacity(1) * max(-phase, 0)
    )
    if primary_zero or secondary_zero:
        new_cost = mp.mpf(0)
    elif prefix_valid:
        new_cost = max(T / L * prefix * phase, 0)
    else:
        new_cost = old_cost
    assigned = sum(
        binom.cdf(13 * N // 32, N + 1, float(1 - x / T))
        - binom.cdf((N + 5) // 5, N + 1, float(1 - x / T))
        for x in logs
    )
    assert abs(direct - reflected) < mp.mpf('1e-100')
    if prefix_valid:
        assert abs(direct + T / L * prefix) < mp.mpf('1e-100')
    if primary_zero or secondary_zero:
        assert abs(direct) < mp.mpf('1e-100')
    assert max(-direct * phase, 0) <= new_cost + mp.mpf('1e-100')
    assert new_cost <= old_cost + mp.mpf('1e-100')
    seven_comparison = None
    if count == 7 and len(outer) == 2:
        # previous_seven_allowances and seven_lowerAllowance_eq: the
        # optimized old negative allowance is ONE least-prime unit, while
        # its positive allowance is three. This is not the Sperner baseline.
        unit = T / L * min(logs)
        previous_seven = unit * (max(phase, 0) + 3 * max(-phase, 0))
        refined_seven = min(previous_seven, new_cost)
        assert max(-direct * phase, 0) <= refined_seven + mp.mpf('1e-100')
        inner = v <= min(active)
        quarter_gap = 4 * max(mp.mpf(0), v) <= min(logs)
        if inner and quarter_gap:
            assert refined_seven <= previous_seven / 4 + mp.mpf('1e-100')
        seven_comparison = dict(
            old_optimized_cost=float(previous_seven),
            refined_cost=float(refined_seven),
            fraction_of_old_charge_removed=float(1 - refined_seven / previous_seven),
            inner_layer=inner, quarter_gap=quarter_gap,
            # The seven-prime head threshold is at most exp(N/128).
            # This is a check of that particular exclusion, not a proof of
            # membership in the complete unpaid core.
            outside_old_seven_prime_head=all(x > mp.mpf(N) / 128 for x in logs),
            below_old_count_tail=count < 8 * (N.bit_length()),
        )
    return dict(
        N=N, count=count, prime_labels=[str(p) for p in primes],
        T_over_N=float(T / N), L_over_T=float(L / T), outer_count=len(outer),
        short_cutoff_share=float(v / T), primary_saturated=primary_zero,
        secondary_count=len(secondary), secondary_saturated=secondary_zero,
        prime_prefix_valid=prefix_valid, coefficient=float(direct),
        phase=float(phase), signed_coefficient=float(direct * phase),
        old_sperner_cost=float(old_cost), new_cost=float(new_cost),
        new_to_old_cost_ratio=float(new_cost / old_cost),
        old_allocated_fraction=float(assigned),
        seven_comparison=seven_comparison,
        checked_geometric_masks=dict(
            radial=mp.mpf('1.95') * N < T <= mp.mpf('2.03') * N,
            nondominant=max(logs) < mp.mpf('.65') * T,
            physical=all(N * N < p < X for p in primes), distinct=len(set(primes)) == count,
        ),
        reflection_error=mp.nstr(abs(direct - reflected), 8),
    )


def main():
    mp.mp.dps = 180
    cases = [
        (512, ['.323', '.321', '.290', '.021', '.022', '.023']),
        (640, ['.322', '.321', '.283', '.024', '.025', '.025']),
        (640, ['.322', '.321', '.285', '.049', '.011', '.012']),
        (640, ['.400', '.284', '.284', '.015', '.017']),
        (640, ['.323', '.321', '.274', '.020', '.020', '.021', '.021']),
        (640, ['.323', '.321', '.270', '.049', '.011', '.012', '.014']),
        (1027, ['.343', '.340', '.221', '.024', '.024', '.024', '.024']),
    ]
    print(json.dumps(dict(
        scope='uncertified individual-prime-label regression; no global or cofinal floor',
        height=54, radius='10001/20000',
        limitations=['height is not asserted to be a zeta zero',
                     'only the displayed geometric masks are checked',
                     'no aggregate population or source-scale saving is inferred',
                     'old_sperner_cost uses SignedSperner; seven_comparison uses the optimized seven-prime cost',
                     'neither individual comparison certifies a global floor'],
        rows=[row(N, shares) for N, shares in cases],
    ), indent=2))


if __name__ == '__main__':
    main()
