#!/usr/bin/env python3
"""Optional algebra-first regression for the fixed-mask order identity.

Finite actual prime atoms are controls, not native-core enumeration or
actual-zero data. Large-order rows are scalar log geometry, not prime labels.
Every signed component and full product phase is retained before comparison.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

from flint import acb, arb, ctx, fmpz
import mpmath as mp
from sympy import nextprime


def real_record(value: arb) -> dict:
    mid, rad = value.mid().man_exp(), value.rad().man_exp()
    return {"mid": [str(mid[0]), int(mid[1])], "rad": [str(rad[0]), int(rad[1])],
            "ball": value.str(70)}


def complex_record(value: acb) -> dict:
    return {"re": real_record(value.real), "im": real_record(value.imag)}


def length(u: Fraction, n: int) -> tuple[arb, int]:
    cutoff = pow(u.denominator, n)//(pow(u.numerator, n)*(n+1))
    return 2*arb(cutoff+2).log(), cutoff.bit_length()


def prime_near(t: mp.mpf) -> int:
    p = int(nextprime(int(mp.exp(t))))
    assert fmpz(p).is_prime()
    return p


def legs(x: arb, height: int, n: int) -> list[acb]:
    a = [acb(-arb(3)*x/2, -height*x).exp()]
    for k in range(1, n+3):
        a.append(a[-1]*x/k)
    return a


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-selberg-adjacent-order/probe.json"))
    args = parser.parse_args()
    ctx.prec, mp.mp.dps = 360, 130
    radii = [Fraction(1, 2), Fraction(10001, 20000)]
    rows = []
    for n in (64, 128, 256):
        ps = [prime_near(mp.mpf(n)+mp.mpf(a)/10) for a in (2, 5, 8)]
        qs = [prime_near(mp.mpf(n)+1+mp.mpf(a)/10) for a in (2, 5, 8)]
        for p in ps:
            for q in qs:
                x, z = arb(p).log(), arb(q).log()
                total = arb(p*q).log()
                assert n < x < n+1 < z < n+2
                assert not n+1 < x
                for uf in radii:
                    u = arb(uf.numerator)/uf.denominator
                    L, bits = length(uf, n)
                    assert max(x, z) < L < total
                    for height in (54, 55, -54, 217):
                        phase = acb(-arb(3)*total/2, -height*total).exp()
                        kernel = {k: total**k/math.factorial(k)*phase
                                  for k in (n-1, n, n+1, n+2)}
                        # Literal inner semiprime Riesz response and Selberg pair term.
                        riesz = L-(L-x)-(L-z)
                        defect = -total*riesz/L+2*x*z/total
                        left = defect*kernel[n]
                        first = arb(3)*(n+1)/2*kernel[n+1]
                        second = -(n+1)*(n+2)/L*kernel[n+2]
                        imbalance = -(x-z)**2/(2*n)*kernel[n-1]
                        joined = first+second+imbalance
                        assert (left-joined).contains(0)
                        ap, aq = legs(x, height, n), legs(z, height, n)
                        cut = 13*n//32
                        pq = sum((ap[n+1-k]*aq[k] for k in range(cut+1)), acb(0))
                        qp = sum((aq[n+1-k]*ap[k] for k in range(cut+1)), acb(0))
                        prefix = (n+1)/L*((L-x)*pq+(L-z)*qp)
                        qz = sum((arb(math.comb(n+1, k))*(z/total)**k*(x/total)**(n+1-k)
                                  for k in range(cut+1)), arb(0))
                        qx = sum((arb(math.comb(n+1, k))*(x/total)**k*(z/total)**(n+1-k)
                                  for k in range(cut+1)), arb(0))
                        prefix_left = (defect-total/L*((L-x)*qz+(L-z)*qx))*kernel[n]
                        assert (prefix_left-(joined-prefix)).contains(0)
                        scale = u**(n+1)
                        values = {"rawDefect": scale*left,
                                  "orderPlusOne": scale*first,
                                  "orderPlusTwo": scale*second,
                                  "imbalanceOrderMinusOne": scale*imbalance,
                                  "joinedOrders": scale*joined,
                                  "factorialPrefix": scale*prefix,
                                  "literalPrefixDefect": scale*prefix_left}
                        rows.append({"N": n, "p": str(p), "q": str(q),
                                     "u": str(uf), "height": height, "cutoffBits": bits,
                                     "balancedMaskAtN": True, "balancedMaskAtNPlusOne": False,
                                     "nativeTheoremThresholdMet": False,
                                     "values": {key: complex_record(v) for key, v in values.items()},
                                     "retainedCoefficientFraction": real_record(defect/(arb(3)*total/2))})
    scalars = []
    for n in (65536, 131072):
        for uf in radii:
            L, bits = length(uf, n)
            x, z = arb(n)+arb(1)/5, arb(n)+arb(8)/5
            total = x+z
            fraction = (arb(3)/2-total/L-(x-z)**2/(2*total**2))/(arb(3)/2)
            assert fraction > arb(1)/30
            scalars.append({"N": n, "u": str(uf), "cutoffBits": bits,
                            "length": real_record(L),
                            "retainedCoefficientFraction": real_record(fraction),
                            "actualPrimeLabel": False})
    result = {"schemaVersion": 1, "precisionBits": 360, "actualPrimeAtomRows": len(rows),
              "scalarGeometryRows": len(scalars), "rows": rows, "scalars": scalars,
              "classification": "exact-component regression; fixed-mask signed identity",
              "nativeCoreEnumerated": False, "actualZeroSamples": 0,
              "nativeEntryOrderCertified": False, "newGlobalCeilingCredit": 0,
              "warning": "Finite atoms and scalar shares do not bound the full signed carrier."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"atomRows": len(rows), "scalarRows": len(scalars),
                      "signedIdentitiesChecked": True, "newGlobalCeilingCredit": 0}))


if __name__ == "__main__":
    main()
