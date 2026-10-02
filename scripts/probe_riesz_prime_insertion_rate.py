#!/usr/bin/env python3
"""Optional genuine-prime coefficient rate audit, not a native-carrier probe.

Every prime in Q={p<=X} has the actual weight 1/p and actual log(p).
The complete signed insertion sum is evaluated through its proved Bernoulli
hinge identity. All counts are retained; a subset with product>=D contributes
exactly zero at d=log(D). Sieve reindexing enumerates every positive-hinge
subset as a squarefree integer, without enumerating all 2^pi(X) subsets.

The only source-normalized numbers are evaluations of the rigorous Lean
LOWER BOUND, not evaluations of the literal prime/masked/factorial carrier.
Floating logarithms and exponentials here are diagnostics, not certificates.
"""

import argparse
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True


def arithmetic_sieve(limit):
    """Exact integers: primes, Euler phi and squarefree support."""
    phi = list(range(limit + 1))
    squarefree = bytearray(b'\x01') * (limit + 1)
    squarefree[0] = 0
    primes = []
    for p in range(2, limit + 1):
        if phi[p] != p:
            continue
        primes.append(p)
        for n in range(p, limit + 1, p):
            phi[n] -= phi[n] // p
        for n in range(p * p, limit + 1, p * p):
            squarefree[n] = 0
    return primes, phi, squarefree


def empty_log(primes):
    return math.fsum(math.log1p(-1.0 / p) for p in primes)


def positive_hinge_sum(D, phi, squarefree):
    # Weight of subset U relative to empty mass is exactly 1/phi(prod U).
    terms = [math.log(D / n) / phi[n]
             for n in range(1, D) if squarefree[n]]
    return math.fsum(terms), len(terms)


def unit_regression(primes, D, phi, squarefree):
    """Independent all-count signed kernel vs average and sieve reindex."""
    weights = {p: Fraction(1, p) for p in primes}
    empty = math.prod(1 - weights[p] for p in primes)
    nested_terms = []
    bernoulli_terms = []
    count_positive = 0
    for k in range(len(primes) + 1):
        for subset in itertools.combinations(primes, k):
            product = math.prod(subset)
            weight = math.prod(weights[p] for p in subset)
            kernel_terms = []
            for m in range(k + 1):
                for sub in itertools.combinations(subset, m):
                    number = math.prod(sub)
                    if number < D:
                        kernel_terms.append((-1) ** m * math.log(D / number))
            nested_terms.append(float((-1) ** k * weight) * math.fsum(kernel_terms))
            if product < D:
                count_positive += 1
                mass = math.prod(weights[p] if p in subset else 1 - weights[p]
                                 for p in primes)
                bernoulli_terms.append(float(mass) * math.log(D / product))
    sieve_sum, sieve_count = positive_hinge_sum(D, phi, squarefree)
    nested = math.fsum(nested_terms)
    average = math.fsum(bernoulli_terms)
    reindexed = float(empty) * sieve_sum
    assert max(abs(nested-average), abs(average-reindexed)) < 2e-11
    assert count_positive == sieve_count
    return dict(X=primes[-1], D=D, primeCount=len(primes),
                allSubsetCount=2 ** len(primes), positiveHingeSubsets=count_positive,
                nestedSigned=nested, bernoulliAverage=average,
                sieveReindexed=reindexed, exactEmptyMass=str(empty),
                floatingReplayOnly=True)


def rate_log(N, numerator, denominator):
    u = Fraction(numerator, denominator)
    g = math.log1p(float(2 * u - 1))
    value = N * g - 16 - 16 * math.log(8 * (N + 2))
    return dict(N=N, u=str(u), sourceGrowthExponent=g,
                logProvedCoefficientLowerBoundAtSource=value,
                finitePrimePoolEvaluatedAtThisOrder=False,
                literalCarrierEvaluated=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-prime', type=int, default=1_000_000)
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/riesz-insertion-rate/prime-coefficients.json'))
    args = parser.parse_args()
    if args.max_prime < 100_000:
        parser.error('--max-prime must be at least 100000 for the complete default audit')
    primes, phi, squarefree = arithmetic_sieve(args.max_prime)
    units = [unit_regression([p for p in primes if p <= X], D, phi, squarefree)
             for X, D in [(7, 7), (11, 10), (13, 12), (17, 16), (19, 18)]]
    rows = []
    for X in [100, 1000, 10_000, 100_000, args.max_prime]:
        pool = [p for p in primes if p <= X]
        log_empty = empty_log(pool)
        empty = math.exp(log_empty)
        harmonic = math.fsum(1.0 / p for p in pool)
        responses = []
        for D in [10, 100, 1000, 10_000, 100_000]:
            if D > X:
                continue
            hinge_sum, size = positive_hinge_sum(D, phi, squarefree)
            response = empty * hinge_sum
            ratio = response / math.log(D)
            assert ratio + 1e-14 >= empty
            assert ratio <= 1 + 1e-13
            responses.append(dict(D=D, hinge=math.log(D), response=response,
                                  responseOverOriginalHinge=ratio,
                                  emptyChannelLowerBound=empty,
                                  everyPositiveHingeSubsetRetained=True,
                                  positiveHingeSubsetCount=size,
                                  excludedSubsetHingeExactlyZero=True,
                                  countTruncation=False))
        rows.append(dict(X=X, primeCount=len(pool), primeWeights='1/p',
                         primeLogs='log(p)', emptyChannel=empty,
                         logEmptyChannel=log_empty, primeHarmonic=harmonic,
                         crudeHarmonicLowerBoundLog=-2 * harmonic,
                         leanLoglogLowerBoundLog=-16 * (1 + math.log(4 * math.log(X) + 8)),
                         responses=responses))
    report = dict(schemaVersion=1,
                  head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
                  purpose='genuine-prime independent coefficient audit; not native capacity',
                  unitRegressions=units, completeGenuinePrimeCoefficientRows=rows,
                  sourceLowerBoundEvaluation=[rate_log(N, *radius)
                      for radius in [(20001, 40000), (10001, 20000)]
                      for N in [256, 640, 1536, 4096, 8192, 100_000,
                                1_000_000, 10_000_000, 100_000_000]],
                  scope=dict(optionalOutsideBuildsCI=True, allInsertionCountsRetained=True,
                             actualPrimeWeightsAndLogs=True, virtualLogs=False,
                             exactPhiAndSquarefreeSieve=True, floatingLogsNotCertified=True,
                             unitRegressionsAreNotUnpaidPopulationScans=True,
                             nativeUnpaidRecordsEvaluated=0, nativePhaseAllocationOrFunding=False,
                             nativeFloorOrZeroExclusion=False))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report['sources'] = {}
    for path in [Path(__file__), Path('RiemannGaussian/ZetaRieszInsertionRateAudit.lean')]:
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        snapshot = args.output.parent / f'source-{digest}{path.suffix}'
        snapshot.write_bytes(data)
        report['sources'][str(path)] = dict(sha256=digest, snapshot=str(snapshot))
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False) + '\n')
    print(json.dumps(dict(unitRegressions=len(units),
                          coefficientRows=len(rows), nativeUnpaidRecordsEvaluated=0,
                          largestPoolPrimeCount=rows[-1]['primeCount'],
                          largestPoolEmptyMass=rows[-1]['emptyChannel'],
                          largestPoolHingeRatios={r['D']: r['responseOverOriginalHinge']
                                                 for r in rows[-1]['responses']},
                          output=str(args.output)), indent=2))


if __name__ == '__main__':
    main()
