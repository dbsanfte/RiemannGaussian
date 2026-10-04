#!/usr/bin/env python3
"""Optional scalar joined-kernel audit; does not sample primes or zeros.

Collect the adjacent factorial slots exactly BEFORE taking the kernel norm.
The model tests a positive Laplace-payment method, not the native carrier.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 115

    def real(x):
        x = F(x)
        return mp.mpf(x.numerator)/x.denominator

    def dec(x):
        return mp.nstr(x, 100)

    uf, af, qf = F(10001, 20000), F(1, 2), F(7, 10)
    u, a, q = map(real, (uf, af, qf))
    gf, bf = 2*uf, 1-1/(2*uf)
    g, b = real(gf), real(bf)
    # Each slot keeps its factorial index and common damping/normalization.
    # p(X)=(1-X/2)/b. Its two Laplace slots cancel at a=1/2,
    # and sum to exactly one at the SELECTED damping u.
    source_slots = [1/bf, -1/(gf*bf)]
    pole_slots = [1/bf, -1/bf]  # common factor g^(N+1), not discarded
    assert sum(source_slots) == 1 and sum(pole_slots) == 0
    assert bf == F(1, 10001)
    assert (1-F(1, 2)/uf)/bf == 1
    assert (1-F(1, 2)/af)/bf == 0

    orders = [64, 256, 640, 1536, 4096, 8192, 16384, 65536, 400000]
    rows = []
    for N in orders:
        j = N+1
        # EXACT full-kernel absolute price at a=1/2. The leading power
        # is u^(N+1), never u^N. E|1-X/j|=2*j^j*e^-j/j!, X~Gamma(j,1).
        log_price = j*mp.log(g)+mp.log(2/b)+j*mp.log(j)-j-mp.loggamma(j+1)
        price_a = mp.exp(log_price)
        # A sufficient separated norm-price bound; not its exact value.
        upper_q = (u/q)**j*(1+1/(2*q))/b
        paid = upper_q <= mp.exp(-mp.mpf(N)/32)
        lower = mp.exp(mp.mpf(N)/255936)/2
        assert paid and price_a >= lower
        rows.append({"N": N, "sourcePower": j,
                     "factorialSlots": [N, N+1],
                     "joinedSourceExact": "1", "joinedPoleExact": "0",
                     "positiveFullKernelPrice": dec(price_a),
                     "separatedPriceUpper": dec(upper_q),
                     "separatedPricePaidAtExpMinusNOver32": paid,
                     "leanMethodPriceLower": dec(lower),
                     "methodLowerExceedsTarget": lower > real(F(42, 25)),
                     "literalCarrierBound": False})

    moving_rows = []
    for N in orders:
        j = N+1
        # These are arbitrary joined Gamma kernels f_N(t), with EXACT
        # selected response one. They illustrate the theorem's necessity
        # of a VANISHING separated budget; bounded alone is insufficient.
        for schedule, rate in [("fixed-u", u), ("sqrt-order", mp.sqrt(j)),
                               ("linear-order", mp.mpf(j))]:
            pa = (rate/(rate-u+a))**j
            pq = (rate/(rate-u+q))**j
            moving_rows.append({"N": N, "sourcePower": j, "schedule": schedule,
                                "sourceExact": "1", "priceA": dec(pa),
                                "priceQ": dec(pq), "actualPrimeKernel": False})

    data = {"schemaVersion": 1,
            "parameters": {"radiusCeiling": str(uf), "arithmeticDamping": str(af),
                           "separatedDamping": str(qf), "target": "42/25",
                           "sourceNormalization": "u^(N+1)",
                           "filterCoefficients": ["10001", "-10001/2"],
                           "orders": orders},
            "exactBookkeeping": {"sourceSlotValues": list(map(str, source_slots)),
                                  "poleSlotCoefficients": list(map(str, pole_slots)),
                                  "poleCommonFactor": "(2u)^(N+1)",
                                  "sourceJoined": "1", "poleJoined": "0",
                                  "coefficientsCollectedBeforeNorm": True},
            "normPriceRows": rows, "movingKernelRows": moving_rows,
            "linearOrderLimits": {"priceA": dec(mp.exp(u-a)),
                                  "priceQ": dec(mp.exp(-(q-u))),
                                  "separatedBudgetDoesNotVanish": True},
            "actualPrimeData": False, "actualZeroData": False,
            "primeDensityTransport": False, "literalCarrierPriceIdentified": False,
            "newArithmeticCeilingCredit": False, "nativeEntryOrderCertified": False,
            "fullAllHeightCeilingProved": False, "simpleZeroFloorProved": False,
            "zeroExclusionProved": False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+"\n")
    print(json.dumps({"adjacentSlotSource": "1", "adjacentSlotPole": "0",
                      "order4096JoinedNormPrice": rows[4]["positiveFullKernelPrice"],
                      "lastMethodLower": rows[-1]["leanMethodPriceLower"],
                      "newArithmeticCeilingCredit": False}))


if __name__ == "__main__":
    main()
