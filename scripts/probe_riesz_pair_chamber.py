#!/usr/bin/env python3
"""Optional actual-label regression for the joined pair-chamber saving.

Enumerates all signed squarefree divisors of each distinct-prime label.
Retains the integer-dependent length, original cosine, factorial kernel
and old binomial allocation. Individual labels do NOT give an aggregate
prime-population bound, coreBand certificate or asymptotic floor. Outside CI.
"""
import json
import math

import mpmath as mp
from scipy.stats import binom
from sympy import nextprime

from probe_riesz_reflected_prefix import riesz


def row(order, shares, height=54):
    primes = []
    for share in shares:
        p = int(nextprime(int(mp.exp(mp.mpf(share) * 2 * order))))
        while p in primes:
            p = int(nextprime(p))
        primes.append(p)
    logs = [mp.log(p) for p in primes]
    total = mp.fsum(logs)
    count = len(primes)
    physical_upper = (20000**order // (10001**order * (order+1)) + 2)**2
    length = mp.log(physical_upper)
    cutoff = total-length
    phase = mp.cos(height*total)
    pair_chamber = all(cutoff/3 <= x <= cutoff/2 for x in logs)
    coefficient = -total/length*riesz(length, logs)
    affine = -total/length*(-1)**count * (
        math.comb(count-1, 2)*cutoff-(count-2)*total)
    assert pair_chamber
    assert abs(coefficient-affine) < mp.mpf('1e-100')
    cost = max(-coefficient*phase, 0)
    sperner_cost = total/length*(total/count)*max(
        math.comb(count-2, j) for j in range(count-1))*abs(phase)
    old_seven_cost = None
    if count == 7:
        assert 2*total <= 3*length and 10*length <= 7*total
        assert all(mp.mpf(2)/15*total <= x <= mp.mpf(3)/20*total for x in logs)
        old_seven_cost = total/length*min(logs)*(5*max(phase, 0)+10*max(-phase, 0))
        # No reflected-large prime; both former saturation tests fail.
        # Thus the old prefix cost is its Sperner fallback, and the
        # already optimized charge is the smaller seven-prime cost.
        assert all(x < cutoff and x < length for x in logs)
        assert total > length and total > cutoff
        assert old_seven_cost <= sperner_cost + mp.mpf('1e-100')
        assert cost <= mp.mpf(3)/4*old_seven_cost + mp.mpf('1e-100')
    assigned = sum(
        binom.cdf(13*order//32, order+1, float(1-x/total))
        - binom.cdf((order+5)//5, order+1, float(1-x/total))
        for x in logs)
    weight = (1-mp.mpf(assigned))*mp.exp(-mp.mpf(3)/2*total)*total**order/mp.factorial(order)
    actual_real = weight*coefficient*phase
    assert abs(max(actual_real, 0)-weight*cost-actual_real) < mp.mpf('1e-100')
    return dict(
        N=order, count=count, prime_labels=[str(p) for p in primes],
        total_over_N=float(total/order), length_over_total=float(length/total),
        pair_chamber=pair_chamber, affine_coefficient=float(affine),
        direct_coefficient=float(coefficient), cosine=float(phase),
        original_allocated_fraction=float(assigned),
        current_optimized_cost=None if old_seven_cost is None else float(old_seven_cost),
        exact_pair_cost=float(cost),
        removed_fraction=None if old_seven_cost is None else float(1-cost/old_seven_cost),
        source_scaled_real=mp.nstr((mp.mpf(10001)/20000)**(order+1)*actual_real, 12),
        checked_masks=dict(
            squarefree_distinct=len(set(primes)) == count,
            radial=mp.mpf('1.95')*order < total <= mp.mpf('2.03')*order,
            nondominant=max(logs) < mp.mpf('.65')*total,
            physical=all(order**2 < p < physical_upper for p in primes),
            outside_small_prime_head=all(x > mp.mpf(order)/128 for x in logs),
            below_count_tail=count < 8*order.bit_length()),
        divisor_identity_error=mp.nstr(abs(coefficient-affine), 8))


def main():
    mp.mp.dps = 180
    balanced = ['.135', '.138', '.140', '.144', '.146', '.148', '.149']
    cases = [(n, balanced) for n in (512, 640, 1027, 1536)]
    cases += [(640, ['.12', '.121', '.123', '.124', '.126', '.127', '.129', '.13'])]
    print(json.dumps(dict(
        scope='individual actual-prime-label diagnostic; NOT an aggregate floor certificate',
        radius='10001/20000', height=54,
        limitations=['height is not assumed to be a zeta zero',
                     'no population or cofinal cancellation follows from these samples',
                     'only the displayed core conditions are checked',
                     'percentage reductions concern each old charge, not the global deficit'],
        rows=[row(n, shares) for n, shares in cases]), indent=2))


if __name__ == '__main__':
    main()
