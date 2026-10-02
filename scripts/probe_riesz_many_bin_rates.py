#!/usr/bin/env python3
"""Optional quantitative screening of many-bin L2 envelope proposals.

This computes envelope rates and the COMPLETE reference Mobius lcm Gram
sum. Neither is the literal count-56+ carrier with its funding witness.
No cancellation, prime asymptotic, native population or floor is certified.
Deliberately outside ordinary CI. Calculations are floating except the
small rational regression of the Gram diagonalization.
"""

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

import numpy as np
from scipy.optimize import brentq

from probe_riesz_signed_density import prime_table


def arithmetic_tables(limit):
    spf = prime_table(limit)
    mu = np.ones(limit + 1, dtype=np.int64)
    phi = np.ones(limit + 1, dtype=np.int64)
    mu[0], phi[0] = 0, 0
    for n in range(2, limit + 1):
        p, a = spf[n], n // spf[n]
        mu[n] = 0 if a % p == 0 else -mu[a]
        phi[n] = phi[a] * (p if a % p == 0 else p - 1)
    return mu, phi


def reference_gram(mu, phi, cutoff, exact=False):
    if exact:
        diagonal = sum(
            phi[g] * sum((Fraction(int(mu[d]), d)
                          for d in range(g, cutoff + 1, g)), Fraction(0)) ** 2
            for g in range(1, cutoff + 1)
        )
        double = sum(
            (Fraction(int(mu[d] * mu[e]), math.lcm(d, e))
             for d in range(1, cutoff + 1)
             for e in range(1, cutoff + 1)), Fraction(0)
        )
        assert diagonal == double
        assert diagonal >= 0
        return str(diagonal)
    coefficients = mu[1:cutoff + 1] / np.arange(1, cutoff + 1)
    return math.fsum(float(phi[g]) * float(coefficients[g - 1::g].sum()) ** 2
                     for g in range(1, cutoff + 1))


def rate_case(order, c=1.0, polynomial_power=5):
    growth = math.log1p(1 / 10000)
    log_order = math.log(order + 1)
    # Use the MOST optimistic allowed bin count, not the lower occupancy.
    bins = math.floor(2 * log_order + 1)
    lower_occupancy = math.floor(log_order / 16) + 1
    log10_discount = -c * bins * log_order / math.log(10)
    log10_source = (growth * order - polynomial_power * log_order) / math.log(10)
    return {
        "order": order,
        "minimumManyBinOccupancy": lower_occupancy,
        "optimisticMaximumBinCount": bins,
        "perBinInversePower": c,
        "log10BinDiscount": log10_discount,
        "log10UndiscountedPositiveEnvelope": log10_source,
        "log10DiscountedPositiveEnvelope": log10_source + log10_discount,
        "log10RequiredSquaredEnergyRatioBeforePolynomialFactors":
            -2 * growth * order / math.log(10),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gram-limit", type=int, default=100000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.gram_limit < 64:
        parser.error("gram limit must be at least 64")
    mu, phi = arithmetic_tables(args.gram_limit)
    rational_checks = [{"cutoff": r, "exactReferenceGram": reference_gram(mu, phi, r, True)}
                       for r in (1, 2, 8, 16, 32, 64)]
    cuts = sorted({1, 2, 10, 100, 1000, 10000, args.gram_limit})
    reference = [{"cutoff": r, "completeReferenceGram": reference_gram(mu, phi, r)}
                 for r in cuts if r <= args.gram_limit]
    orders = [1000, 10000, 100000, 1000000, 10000000]
    orders += [8 * (j + 4) * 2 ** (j + 3) for j in (16, 24, 32)]
    cases = [rate_case(n) for n in sorted(set(orders))]
    growth = math.log1p(1 / 10000)

    def lower_envelope_exponent(n):
        ln = math.log(n + 1)
        return growth * n - 2 * ln ** 2 - 6 * ln

    crossover = brentq(lower_envelope_exponent, 1000000, 100000000)
    report = {
        "scope": "Complete reference Gram and proposed POSITIVE envelope rates only.",
        "radius": "10001/20000",
        "amplitudeGrowthExponent": growth,
        "squaredEnergyExponentNeededBeforePolynomialFactors": 2 * growth,
        "completeReferenceGramDefinition": "sum_(d,e<=R) mu(d)mu(e)/lcm(d,e)",
        "exactRationalChecks": rational_checks,
        "completeReferenceGramSamples": reference,
        "envelopeCases": cases,
        "continuousLowerEnvelopeCrossover": crossover,
        "crossoverFormula": "log(1.0001)N - 2 log(N+1)^2 - 6 log(N+1) = 0",
        "crossoverIntervalCertified": False,
        "nativeCount56PopulationEvaluated": False,
        "nativePhysicalMasksEvaluated": False,
        "fundingWitnessIncluded": False,
        "referenceGramImportedAsLeanTheorem": False,
        "actualEnergySavingCertified": False,
        "sourceScalePopulationPaid": False,
        "floorCertified": False,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({
        "referenceGramLast": reference[-1],
        "amplitudeGrowthExponent": growth,
        "squaredEnergyExponent": 2 * growth,
        "envelopeCrossover": crossover,
        "nativeOrderAtJ32": rate_case(8 * 36 * 2 ** 35),
        "floorCertified": False,
    }, indent=2))


if __name__ == "__main__":
    main()
