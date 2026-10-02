#!/usr/bin/env python3
"""Optional joint many-bin/owner-period diagnostic, never an ordinary CI job.

The cofactors are continuous log models, NOT certified prime labels. The
exact signed subset polynomial is retained, as are both reflected hinges,
the complete owner phase period, moving length to exponentially small
rounding error, and the full radial factorial amplitude. This tests a
proposed geometric orthogonality inference, not the actual arithmetic floor.
The original allocation is enclosed by a binomial tail, not assumed absent.
"""

import argparse
import json
from functools import lru_cache
from pathlib import Path

import mpmath as mp

from probe_riesz_dense_count_cover import dyadic_scale
from probe_riesz_few_bin_cover import grid_subset_counts

mp.mp.dps = 90
U = mp.mpf(10001) / 20000
Y = mp.mpf(54)
HALF_PERIOD = mp.pi / Y


@lru_cache(maxsize=None)
def background(count, bins):
    # All indices are odd, but there are arbitrarily many occupied scales.
    # The large binary scales are separated by more than the entire low
    # subset range. Their coefficient can be extracted without a gigantic
    # knapsack array. Counts grow with log N in the last two tests.
    low = list(range(3, 2 * (count - bins) + 3, 2))
    base = 2 * (len(low) + 2)**2
    high = [base * 2**i + 1 for i in range(bins)]
    assert sum(low) + bins < base
    _, low_unsigned = grid_subset_counts(low)
    return low, high, base, low_unsigned


def relative_entropy(x, p):
    return x * mp.log(x / p) + (1 - x) * mp.log((1 - x) / (1 - p))


def model_row(N, v, count, sign, data):
    low, high, base, low_unsigned = data
    odd = low + high
    # This is L_N without its integer-cutoff rounding. For the actual
    # D=floor(exp(-N log u)/(N+1)), log((D+2)^2) differs by at most
    # 4*(N+1)*exp(N log u), once the undamped cutoff exceeds two.
    L = -2 * N * mp.log(U) - 2 * mp.log(N + 1)
    total_units = 9 + 32 * sum(odd)
    code = int(mp.floor(mp.mpf('0.68') * (2**len(high) - 1)))
    high_sum = base * code + code.bit_count()
    target = sum(low) // 2
    for shift in range(-8, 9):
        j = high_sum + target + shift
        low_index = j - high_sum
        mass = low_unsigned[low_index]
        if not mass or (-1)**(count + j) != sign:
            continue
        scale = (v - L) / (32 * j + mp.mpf('4.5'))
        cofactor = total_units * scale
        share = 1 - cofactor / v
        if not mp.mpf('0.54') <= share <= mp.mpf('0.56'):
            continue
        logs = [3 * scale, 6 * scale, *[32 * x * scale for x in odd]]
        assert len(logs) == count
        head = max(mp.mpf(5000), 32 * mp.log(N + 1))
        bins = {dyadic_scale(x, head) for x in logs if head < x}
        assert len(bins) > int(mp.floor(mp.log(N + 1) / 16))
        assert 56 <= count + 1 < 5 * mp.log(N + 1) + 2
        assert v - cofactor - HALF_PERIOD > max(logs)
        assert min(logs) > 2 * mp.log(N)  # original N^2 physical head
        assert mp.mpf('1.95') * N < v - HALF_PERIOD
        assert v + HALF_PERIOD < mp.mpf('2.03') * N
        assert share < mp.mpf(751) / 1250
        assert cofactor - L < 0  # second hinge retained and exactly zero
        assert 3 * scale > HALF_PERIOD and mp.mpf('1.5') * scale > HALF_PERIOD
        # The signed first hinge is constant on the ENTIRE owner period:
        # precisely one background cell meets the plateau of the 3,6 tent.
        response = sign * mass * 3 * scale
        assert mp.sign(response) == sign
        # For every prime incidence, the cofactor share exceeds 13/32.
        # A Chernoff envelope encloses the original boundedShare uniformly
        # over the period. Nonowner incidences are included in the count.
        min_cofactor_share = 1 - (v - cofactor + HALF_PERIOD) / (v + HALF_PERIOD)
        allocation_log_bound = mp.log(count + 1) - (N + 1) * relative_entropy(
            mp.mpf(13) / 32, min_cofactor_share)
        assert allocation_log_bound < -1000

        owner_center = v - cofactor

        def amplitude(t):
            # Full amplitude(N,v+t)/amplitude(N,v), with the literal
            # d(log p)/log p ordinary-prime model measure retained.
            return mp.exp(-t / 2 + (N + 1) * mp.log1p(t / v)) * (
                owner_center / (owner_center + t))

        integral = mp.quad(lambda t: amplitude(t) * mp.cos(Y * t),
                           [-HALF_PERIOD, 0, HALF_PERIOD])
        unsigned = mp.quad(lambda t: amplitude(t) * abs(mp.cos(Y * t)),
                           [-HALF_PERIOD, -HALF_PERIOD / 2, 0,
                            HALF_PERIOD / 2, HALF_PERIOD])
        relative = sign * integral / unsigned
        # Source-normalized factorial PERIOD UNIT, not the actual row
        # mass: the latter also has the essential cofactor factor 1/a.
        log_unit = ((N + 1) * mp.log(U) - v / 2 +
                    (N + 1) * mp.log(v) - mp.loggamma(N + 1))
        metadata = dict(
            N=N, totalPrimeCount=count + 1, cofactorCount=count,
            occupiedBins=len(bins), paidBinCeiling=int(mp.floor(mp.log(N + 1) / 16)),
            ownerShare=float(share), largestCofactorShare=float(max(logs) / v),
            modelLogConditionsChecked=True, actualPrimeLabel=False,
            fullOriginalSpentSetCertified=False,
            movingLengthRoundingErrorLog10=float(
                (mp.log(4 * (N + 1)) + N * mp.log(U)) / mp.log(10)),
            allocationUpperBoundLog10=float(allocation_log_bound / mp.log(10)),
            fullPeriodSignedToUnsigned=float(relative),
            sourcePeriodUnitLog10=float(log_unit / mp.log(10)),
            actualCofactorFactorNotPaid=True,
            populationMassNotEstimated=True,
        )
        return metadata, amplitude
    raise ValueError(f'No coherent interior cell at N={N}, count={count}')


def scan(N, radial_ratio):
    # An even total-log peak, so every count and bin has the SAME cosine.
    k = int(mp.nint(radial_ratio * N * Y / (2 * mp.pi)))
    v = 2 * mp.pi * k / Y
    rows, profiles = [], []
    desired_sign = 1 if radial_ratio < 2 else -1
    minimum_count = max(55, int(mp.ceil(2 * mp.log(N))))
    bins = int(mp.floor(mp.log(N + 1) / 16)) + 4
    for count in range(minimum_count, minimum_count + 6):
        data = background(count - 2, bins)
        row, profile = model_row(N, v, count, desired_sign, data)
        rows.append(row)
        profiles.append(profile)
    # Joint L2 BEFORE separating counts/bin patterns. A purported diagonal
    # bound misses positive cross terms because the recentered phase agrees.
    gram = []
    for a in profiles:
        gram.append([mp.quad(lambda t: a(t) * b(t) * mp.cos(Y*t)**2,
                             [-HALF_PERIOD, 0, HALF_PERIOD]) for b in profiles])
    diagonal = mp.fsum(gram[i][i] for i in range(len(profiles)))
    joint = mp.fsum(mp.fsum(row) for row in gram)
    correlations = [gram[i][j] / mp.sqrt(gram[i][i] * gram[j][j])
                    for i in range(len(profiles)) for j in range(i)]
    return dict(
        N=N, totalLogOverN=float(v / N), rows=rows,
        jointEnergyOverDiagonalEnergy=float(joint / diagonal),
        leastCrossCountProfileCorrelation=float(min(correlations)),
        jointEnergyDefectFromSix=mp.nstr(6 - joint / diagonal, 30),
        largestCrossCorrelationDefect=mp.nstr(max(1 - c for c in correlations), 30),
        signedJointPeriodMean=float(mp.fsum(row['fullPeriodSignedToUnsigned'] for row in rows)),
        modelOnly=True, fixedHeight=float(Y),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    results = dict(
        diagnosticOnly=True, numericalFloorCertified=False,
        tests=[scan(N, radial) for N in (10**8, 10**10, 10**12,
                                        int(mp.exp(64)), int(mp.exp(128)))
               for radial in (mp.mpf('1.99'), mp.mpf(2))],
        conclusions=[
            'Occupied cofactor bins are not distinct owner-period phase frequencies.',
            'Joint Gram energy can retain essentially all cross terms across counts and bins.',
            'An entire owner period can have a reinforcing signed residual with the full factorial amplitude.',
            'These models do not bound the actual weighted prime population or disprove the floor.',
        ],
    )
    rendered = json.dumps(results, indent=2, allow_nan=False)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered + '\n')
    else:
        print(rendered)


if __name__ == '__main__':
    main()
