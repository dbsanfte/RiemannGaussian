#!/usr/bin/env python3
"""Optional full-convolution null test of the joined signed floor.

This probes a positive CONTINUOUS rational model, not ordinary primes.
The factorial indices and the moving-length error are retained. Numerical
values do not certify an arithmetic floor or an entry order. The matching
Lean leaf proves the model's eventual failure without these samples.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import mpmath as mp


def number(value: mp.mpf) -> str:
    return mp.nstr(value, 35)


def complex_number(value: mp.mpc) -> dict[str, str]:
    return {"re": number(mp.re(value)), "im": number(mp.im(value))}


def numerator(u: mp.mpf, y: mp.mpf, t: mp.mpf) -> mp.mpf:
    return mp.exp(t) + mp.exp((2 - 2 * u) * t) - 2 * mp.exp(
        (mp.mpf(3) / 2 - u) * t
    ) * mp.cos(y * t)


def channels(u: mp.mpf, y: mp.mpf) -> list[mp.mpc]:
    return [u / (mp.mpf("0.5") + 1j * y),
            u / (2 * u - mp.mpf("0.5") + 1j * y),
            u / (u + 2j * y)]


def joined_direct(u: mp.mpf, y: mp.mpf, order: int, length: mp.mpf) -> mp.mpc:
    ratios = channels(u, y)
    array = [ratios[0] ** (k + 1) + ratios[1] ** (k + 1) - 1
             - ratios[2] ** (k + 1) for k in range(order + 2)]
    cutoff = 13 * order // 32
    return (mp.fsum(array[k] * array[order - 1 - k] for k in range(order)) / order
            + mp.fsum(array[k - 1] * array[order - k] / (order + 1 - k)
                      for k in range(cutoff + 1, order - cutoff + 1))
            - (order + 1) / (u * length)
            * mp.fsum(array[k - 1] * array[order + 1 - k] / (order + 2 - k)
                      for k in range(1, order + 2 - cutoff)))


def factorial_slots(u: mp.mpf, y: mp.mpf, order: int, length: mp.mpf) -> dict[str, mp.mpc]:
    """The four ORIGINAL factorial slots before harmonic collection.

    Swapped incidences use the same array and exactly complementary
    indices. This is an algebraic regression, not a population scan.
    """
    ratios = channels(u, y)
    array = [ratios[0] ** (k + 1) + ratios[1] ** (k + 1) - 1
             - ratios[2] ** (k + 1) for k in range(order + 2)]
    cutoff = 13 * order // 32
    m = order + 1
    return {
        "central": m / 2 * mp.fsum(array[k - 1] * array[m - k - 1] / (k * (m - k))
                                    for k in range(cutoff + 1, m - cutoff)),
        "successor": -m * (m + 1) / (2 * u * length)
        * mp.fsum(array[k - 1] * array[m - k] / (k * (m + 1 - k))
                  for k in range(cutoff + 1, m + 1 - cutoff)),
        "loggedPrefix": -m / (u * length)
        * mp.fsum(array[k - 1] * array[m - k] / (m + 1 - k)
                  for k in range(1, cutoff + 1)),
        "fullTrace": mp.fsum(array[k] * array[order - 1 - k]
                             for k in range(order)) / order,
    }


def joined_edges(u: mp.mpf, y: mp.mpf, order: int, length: mp.mpf,
                 head: int = 128) -> tuple[mp.mpc, mp.mpf]:
    """Exact integer endpoints, with a stated geometric truncation bound.

    The bound covers the omitted channels, NOT finite-precision roundoff.
    The baseline includes all four signed slots, not one count sector.
    """
    assert order >= 2 * head
    ratios = channels(u, y)
    radius = max(abs(value) for value in ratios)
    assert radius < 1
    errors = [ratios[0] ** (k + 1) + ratios[1] ** (k + 1) - ratios[2] ** (k + 1)
              for k in range(head)]
    cutoff = 13 * order // 32
    factor = (order + 1) / (u * length)
    harmonic = lambda n: mp.digamma(n + 1) + mp.euler
    baseline = (1 + harmonic(order - cutoff) - harmonic(cutoff)
                - factor * (harmonic(order + 1) - harmonic(cutoff)))
    value = (baseline - 2 * mp.fsum(errors) / order
             + factor * mp.fsum(errors[k] / (order + 1 - k) for k in range(head)))
    bound = (6 * radius ** (head + 1) / (order * (1 - radius))
             + 9 * radius ** (order + 1)
             + order * (6 * radius ** (cutoff + 1) + 9 * radius ** (order + 1))
             + factor * (3 * radius ** (head + 1) / (1 - radius)
                         + 3 * (order + 1) * radius ** (cutoff + 1)
                         + 9 * (order + 1) * radius ** (order + 2)))
    return value, bound


def moving_length(order: int, u: mp.mpf) -> tuple[mp.mpf, mp.mpf, str]:
    if order <= 8192:
        denominator = (20000 ** order) // ((order + 1) * (10001 ** order))
        return 2 * mp.log(denominator + 2), mp.mpf(0), "exact integer D, transcendental evaluation"
    # D=floor(1/((N+1)u^N)), so 0<=L-2log(1/((N+1)u^N))<=4(N+1)u^N.
    length = -2 * order * mp.log(u) - 2 * mp.log(order + 1)
    return length, 4 * (order + 1) * u ** order, "asymptotic length with explicit floor-error bound"


def probe() -> dict:
    mp.mp.dps = 100
    u = mp.mpf(10001) / 20000
    y = mp.mpf(54)
    target = mp.mpf(399) / 5000
    retained = mp.log(mp.mpf(32) / 13) / (-2 * u * mp.log(u)) - mp.log(mp.mpf(19) / 13)
    rows = []
    for order in [256, 640, 8192, 65536, 196608, 425984, 1048576]:
        length, length_error, method = moving_length(order, u)
        value, truncation = joined_edges(u, y, order, length)
        direct_error = None
        slots = None
        algebra_error = None
        if order <= 640:
            direct = joined_direct(u, y, order, length)
            direct_error = abs(value - direct)
            assert direct_error <= truncation + mp.mpf("1e-90")
            slots = factorial_slots(u, y, order, length)
            algebra_error = abs(mp.fsum(slots.values()) - direct)
            assert algebra_error < mp.mpf("1e-90")
        # Conservative change of the finite polynomial when L moves within
        # its stated interval; |array[k]|<=1+3r<4 for this model.
        harmonic = mp.digamma(order + 2) + mp.euler
        length_value_error = 16 * (order + 1) * harmonic * length_error / (u * length ** 2)
        rows.append({"N": order, "joinedValue": complex_number(value),
                     "aboveTargetInThisSample": mp.re(value) > target,
                     "channelTruncationBoundExcludingRoundoff": number(truncation),
                     "directFiniteSumError": None if direct_error is None else number(direct_error),
                     "originalFactorialSlots": None if slots is None else
                     {name: complex_number(term) for name, term in slots.items()},
                     "exactFactorialToHarmonicRegressionError": None if algebra_error is None else
                     number(algebra_error),
                     "movingLengthMethod": method, "movingLengthFloorErrorBound": number(length_error),
                     "movingLengthEvaluationErrorBound": number(length_value_error)})

    beta = mp.mpf(3) / 2 - u
    alpha = 2 - 2 * u
    exponents = [mp.mpc(1), mp.mpc(alpha), beta + 1j * y, beta - 1j * y]
    signs = [1, 1, -1, -1]
    kernel_rows = []
    for t in map(mp.mpf, ["0.001", "0.1", "1"]):
        closed = mp.fsum(signs[i] * signs[j]
                         * (t * mp.exp(exponents[i] * t) if i == j else
                            (mp.exp(exponents[i] * t) - mp.exp(exponents[j] * t))
                            / (exponents[i] - exponents[j]))
                         for i in range(4) for j in range(4))
        integral = mp.quad(lambda v: numerator(u, y, v) * numerator(u, y, t - v),
                           [t * k / 64 for k in range(65)])
        error = abs(integral - closed)
        assert error < mp.mpf("1e-80")
        density = numerator(u, y, t)
        kernel = t * density + integral
        assert density >= 0 and kernel >= 0
        kernel_rows.append({"t": number(t), "positiveNumerator": number(density),
                            "joinedSelbergKernel": number(kernel),
                            "exactExponentialConvolutionRegressionError": number(error)})

    delta = u - mp.mpf("0.5")
    regular = 1 / (-delta + 1j * y) + 1 / (delta + 1j * y) - 1 / (2j * y)
    return {"schemaVersion": 1, "kind": "positive CONTINUOUS rational full-convolution null test",
            "ordinaryPrimeMeasure": False, "literalPrimeSamples": 0, "usesActualZetaZero": False,
            "u": "10001/20000", "y": 54, "decimalDigits": mp.mp.dps,
            "target": number(target), "provedJoinedSource": number(1 - retained),
            "contradictionMarginNotMeasuredUnpaidMass": number(1 - retained - target),
            "selectedFullSelbergDoublePoleCoefficient": "0",
            "selectedFullSelbergSimplePoleResidue": complex_number(-2 * regular),
            "modelCountPoleResidue": number((y ** 2 + delta ** 2) / (2 * u - 1)),
            "ordinaryIntegerCountPoleResidue": "1",
            "extraRealPole": number(alpha),
            "algebraicBookkeepingBeforeStatistics": {
                "originalSlotsRetained": ["central", "successor", "loggedPrefix", "fullTrace"],
                "sameArrayAtComplementaryIndices": True,
                "orderZeroLoggedChannelsRetained": True,
                "separateSlotLimitsNotUsedAsAllowance": True,
            },
            "joinedFiniteOrders": rows, "positiveConvolutionRegression": kernel_rows,
            "firstThresholdCrossingCertified": False, "newFloorSaving": False,
            "newZeroExclusion": False, "numericsUsedInLeanProof": False}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-selberg-renewal/renewal-probe.json"))
    args = parser.parse_args()
    report = probe()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(f"Wrote {args.output}; synthetic continuous model only.")
    print("Full Selberg double pole:0; joined source:" + report["provedJoinedSource"])
    print("No literal-prime estimate, floor saving, or zero exclusion.")


if __name__ == "__main__":
    main()
