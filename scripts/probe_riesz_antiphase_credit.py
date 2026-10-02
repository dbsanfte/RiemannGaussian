#!/usr/bin/env python3
"""Optional signed, joined-cutoff antiphase-credit diagnostic.

Keeps the rational moving length, product-label phase and actual divisor
columns. Orders 4/5 have empty factorial allocation, but their labels do
NOT satisfy the original annulus/physical/dyadic masks. At these orders
the native near-label strip covers all pairs, so the nonzero calculation
uses an explicitly diagnostic relative-distance threshold of 1/1000.
Floating results are not an arithmetic floor or a cofinal certificate.
"""

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

import numpy as np

from probe_riesz_post_hinge_correlations import divisors
from probe_riesz_signed_density import prime_table


def experiment(order, heights):
    radius = Fraction(10001, 20000)
    cutoff = radius.denominator**order // (radius.numerator**order * (order + 1))
    length = 2 * math.log(cutoff + 2)
    assert not any(32*k <= 13*order and 5*(order+1-k) < 4*order
                   for k in range(order+2))
    first = math.floor(math.exp(39*order/20)) + 1
    last = math.floor(math.exp(203*order/100))
    spf = prime_table(last)
    mu = np.ones(last+1, dtype=np.int8)
    counts = np.zeros(last+1, dtype=np.int16)
    largest = np.ones(last+1, dtype=np.int64)
    for n in range(2, last+1):
        p, rest = int(spf[n]), n//int(spf[n])
        mu[n] = 0 if rest % p == 0 else -mu[rest]
        counts[n] = counts[rest]+int(rest % p != 0)
        largest[n] = max(largest[rest], p)
    labels = np.arange(first, last+1)
    selected = labels[(mu[labels] != 0) & (counts[labels] >= 3) &
                      (np.log(largest[labels]) < (60069/100000)*np.log(labels))]
    endpoint = int(selected.max())
    increments = np.zeros((endpoint+1, selected.size), dtype=np.int16)
    for i, n in enumerate(selected):
        for d in divisors(int(n), spf):
            increments[d, i] = mu[d]
    cutoffs = np.arange(1, endpoint)
    columns = np.cumsum(increments, axis=0, dtype=np.int16)[cutoffs].astype(float)
    steps = np.maximum(length, np.log(cutoffs))-np.maximum(length, np.log(cutoffs+1))
    logs = np.log(selected)
    gap = logs[:, None]-logs[None, :]
    distinct = ~np.eye(selected.size, dtype=bool)
    small_gcd = np.log(np.gcd(selected[:, None], selected[None, :])) <= order/1000
    distance = np.abs(selected[:, None]-selected[None, :])/np.minimum(
        selected[:, None], selected[None, :])
    native_separated = distinct & small_gcd & (distance > math.exp(-order/1000))
    diagnostic_separated = distinct & small_gcd & (distance > 1/1000)
    amplitude = (float(radius)**(order+1)/(length*math.factorial(order)) *
                 np.exp(-1.5*logs)*logs**(order+1))
    cases = []
    for height in heights:
        cosines = np.cos(height*logs)
        weights = -amplitude*cosines
        prefix = columns @ weights
        adverse = prefix*steps < 0
        # Join every selected cutoff BEFORE inspecting the Gram sign.
        gram = columns[adverse].T @ (columns[adverse]/cutoffs[adverse, None])
        pair_amplitude = amplitude[:, None]*amplitude[None, :]*gram
        cross = pair_amplitude*cosines[:, None]*cosines[None, :]
        old_width = math.exp(-order/1000)/(1+abs(height))
        nearest_period = np.rint(height*gap/(2*math.pi))
        old_orbit = np.abs(gap-2*math.pi*nearest_period/height) <= old_width
        base = diagnostic_separated & ~old_orbit
        width = math.exp(-order/10000)/(1+abs(height))
        odd_period = np.rint((height*gap-math.pi)/(2*math.pi))
        antiphase = np.abs(gap-(2*odd_period+1)*math.pi/height) <= width
        credited = base & antiphase & (gram >= 0)
        cos_sum = cosines[:, None]+cosines[None, :]
        reserve_matrix = pair_amplitude*(cosines[:, None]**2+cosines[None, :]**2)/2
        leak_matrix = pair_amplitude*cos_sum**2/2
        reserve = float(np.sum(reserve_matrix[credited]))
        leakage = float(np.sum(leak_matrix[credited]))
        leakage_bound = ((height*width)**2/2)*float(np.sum(pair_amplitude[credited]))
        energy = float(np.sum(cross[base]))
        antiphase_energy = float(np.sum(cross[credited]))
        rest = float(np.sum(cross[base & ~credited]))
        assert abs(energy-rest+reserve-leakage) < 1e-12
        assert abs(antiphase_energy+reserve-leakage) < 1e-12
        assert 0 <= leakage <= leakage_bound+1e-12
        profile = float(np.sum(cutoffs[adverse]*steps[adverse]**2))
        cases.append({
            "order": order, "height": height, "labels": int(selected.size),
            "countsPresent": [int(k) for k in np.unique(counts[selected])],
            "movingIntegerCutoff": cutoff, "movingLength": length,
            "allocationSupportExactlyEmpty": True,
            "originalAdverseProfile": profile,
            "nativeSeparatedPairs": int(np.count_nonzero(native_separated)),
            "diagnosticRelativeDistanceThreshold": 1/1000,
            "widthLog": width, "creditedOrderedPairs": int(np.count_nonzero(credited)),
            "joinedCutoffAntiphaseCredit": reserve,
            "actualLeakage": leakage, "phaseLeakageUpperBound": leakage_bound,
            "originalRemainingSignedEnergy": energy,
            "restBeforeNegativeCredit": rest,
            "antiphaseSignedEnergy": antiphase_energy,
            "restMinusCredit": rest-reserve,
            "costIfCreditDiscarded": math.sqrt(max(rest, 0)*profile),
            "costWithCreditAndLeakage": math.sqrt(max(rest-reserve+leakage_bound, 0)*profile),
        })
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", type=int, nargs="+", default=[4, 5])
    parser.add_argument("--heights", type=float, nargs="+", default=[54, 65, 100])
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if any(n not in (4, 5) for n in args.orders):
        parser.error("only the complete empty-allocation orders 4/5 are supported")
    if any(not math.isfinite(y) or y < 54 for y in args.heights):
        parser.error("heights must be finite and >=54")
    cases = [c for n in args.orders for c in experiment(n, args.heights)]
    report = {
        "scope": "Floating diagnostic of joined-cutoff negative antiphase credit.",
        "nativePhysicalAnnulusMasksCertified": False,
        "nativeDyadicScheduleCertified": False,
        "nativeCount56PlusManyBinPopulationCertified": False,
        "intervalArithmeticCertified": False, "floorProved": False,
        "cases": cases,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "cases": len(cases),
        "positiveCreditCases": sum(c["joinedCutoffAntiphaseCredit"] > 0 for c in cases),
        "strictCostSavingCases": sum(c["costWithCreditAndLeakage"] <
                                     c["costIfCreditDiscarded"] for c in cases),
        "floorProved": False,
    }, indent=2))


if __name__ == "__main__":
    main()
