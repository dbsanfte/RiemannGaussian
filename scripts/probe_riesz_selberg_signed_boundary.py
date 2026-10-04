#!/usr/bin/env python3
"""Optional signed endpoint controls, with continuum diagnostics separated.

Ball rows check scalar geometry only. Floating quadrature is explicitly
not certified, does not sample actual primes/zeros, and does not supply
the qualitative-PNT entry threshold in the Lean theorem.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
import math
from pathlib import Path

from flint import arb, ctx
import numpy as np
from scipy.special import gammaln


def record(x: arb) -> dict:
    mid, rad = x.mid().man_exp(), x.rad().man_exp()
    return {"mid": [str(mid[0]), int(mid[1])],
            "rad": [str(rad[0]), int(rad[1])], "ball": x.str(70)}


def length(uf: Fraction, n: int) -> tuple[arb, int]:
    cutoff = pow(uf.denominator, n)//(pow(uf.numerator, n)*(n+1))
    return 2*arb(cutoff+2).log(), cutoff.bit_length()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/riesz-selberg-signed-boundary/probe.json"))
    args = parser.parse_args()
    ctx.prec = 360
    uf = Fraction(10001, 20000)
    u, y = arb(uf.numerator)/uf.denominator, 19*arb.pi()
    controls = {"height": y, "sineIntegral": 2/y,
                "phaseEndpoint": 4/y**2,
                "limitingSaddleCoefficient": 3+2/u.log(),
                "continuumLimit": (3+2/u.log())*4/y**2,
                "phaseCertificateSlack": (arb(1)/30-arb(1)/100000)**2
                    -(arb(1)/100000)**2-arb(1)/1000}
    assert controls["height"] > 54 and controls["height"] < 60
    assert controls["phaseCertificateSlack"] > 0
    rows = []
    for n in (65536, 131072):
        L, bits = length(uf, n)
        assert L >= arb(277)*n/200
        B = 3*n-4*arb(n)**2/L
        assert B >= arb(n)/10
        for ar, br in ((Fraction(1, 5), Fraction(8, 5)),
                       (Fraction(1, 2), Fraction(3, 2)),
                       (Fraction(4, 5), Fraction(6, 5))):
            x = arb(n)+arb(ar.numerator)/ar.denominator
            z = arb(n)+arb(br.numerator)/br.denominator
            T = x+z
            F = (-(T-2*n)/2).exp()*(T/(2*n))**n
            delta = arb(3)*T/2-T**2/L-(x-z)**2/(2*T)
            joined = delta*F-B
            assert abs(joined) < 26 and F <= 1
            assert abs(F-1) <= arb(2)/n
            rows.append({"N": n, "a": str(ar), "b": str(br), "cutoffBits": bits,
                         "actualPrimeLabel": False,
                         "values": {"length": record(L), "saddleFactor": record(F),
                                    "saddleCoefficient": record(B),
                                    "joinedSaddleError": record(joined)}})

    # Diagnostic density integral on the FULL unchanged two log windows.
    # Recompute at two quadrature sizes; agreement is not a rigorous enclosure.
    diagnostics = []
    for n in (256, 640, 1536, 4096, 8192, 65536):
        L, _ = length(uf, n)  # Literal moving floor and successor correction.
        lf, yy, uu = float(L), float(y), float(u)
        values = []
        for nodes in (192, 256):
            grid, weights = np.polynomial.legendre.leggauss(nodes)
            a, b = (grid+1)/2, (grid+3)/2
            A, B = a[:, None], b[None, :]
            T = 2*n+A+B
            delta = 1.5*T-T*T/lf-(A-B)**2/(2*T)
            saddle = np.exp(-(A+B)/2+n*np.log1p((A+B)/(2*n)))
            integrand = n*delta/((n+A)*(n+B))*saddle*np.cos(yy*(A+B))
            values.append(float(np.sum(integrand*weights[:, None]*weights[None, :])/4))
        logV = -n+n*math.log(2*n)-gammaln(n+1)
        diagnostics.append({"N": n, "exactMovingLengthBall": record(L),
                            "normalizedShape192": values[0], "normalizedShape256": values[1],
                            "quadratureDifference": abs(values[0]-values[1]),
                            "logRawContinuumMagnitude": logV-math.log(n)+math.log(abs(values[1])),
                            "sourceNormalizedContinuum": math.exp((n+1)*math.log(uu)
                                +logV-math.log(n))*values[1],
                            "certified": False, "actualPrimeSum": False})
    result = {"schemaVersion": 1, "precisionBits": 360, "radius": str(uf),
              "controls": {k: record(v) for k, v in controls.items()}, "scalarRows": rows,
              "continuumDiagnostics": diagnostics, "actualPrimeSamples": 0,
              "actualZeroSamples": 0, "nativeCoreEnumerated": False,
              "nativeEntryOrderCertified": False, "fullConstantCeilingProved": False,
              "newGlobalCeilingCredit": 0,
              "warning": "Only scalar balls are replayed rigorously; continuum quadrature is exploratory."}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"scalarRows": len(rows), "ballControls": len(controls),
                      "uncertifiedContinuumRows": len(diagnostics), "actualPrimeSamples": 0,
                      "nativeEntryOrderCertified": False, "newGlobalCeilingCredit": 0}))


if __name__ == "__main__":
    main()
