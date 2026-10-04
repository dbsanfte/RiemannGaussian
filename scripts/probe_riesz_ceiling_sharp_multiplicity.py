#!/usr/bin/env python3
"""Optional exact-scalar replay of the sharper multiplicity payment.

The Lean theorem uses the actual Gaussian moment recurrence. These rows
sample no primes, zeros or carrier arrays and certify no native entry order.
This probe is outside ordinary builds and CI.
"""
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 90
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-sharp-multiplicity/probe.json"


def decimal(x: F) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator


# Every moment is represented as A_n * G_1(x) + B_n. Keep the signed
# recurrence intact: taking absolute values here loses the enclosure.
x_unit = F(2701, 2000)
affine = [(F(1), F(0)), (-x_unit / 2, F(1, 2))]
for n in range(15):
    prev, curr = affine[n], affine[n + 1]
    affine.append(tuple(((n + 1) * prev[i] - x_unit * curr[i]) / 2
                        for i in range(2)))
A16, B16 = affine[16]
assert A16 > 0
moment_lower = -B16 / A16
unit_lower = F(59, 125)
normalized_lower = F(59, 250)
assert moment_lower > unit_lower
assert normalized_lower == unit_lower / 2

damping = 2 * x_unit
source_slope = 450000 * normalized_lower
weighted_slope = 2 * F(79, 250) * source_slope
assert source_slope == 106200
assert weighted_slope == F(335592, 5) > 67000
assert -2 * F(79, 250) * 6 > -4
cot_bound = 16 * F(1, 40500) * damping / (8 * F(1, 200) ** 2)
assert cot_bound < 6

margin_slope = F(67000 - 36922, 1000000) - F(1, 35) - F(57, 200000)
margin_constant = F((67000 - 36922) * 60000, 1000000) - 4 - 57 * 12 - 840
minimum_margin = 50000 * margin_slope + margin_constant
assert margin_slope == F(8551, 7000000) > 0
assert margin_constant == F(6917, 25)
assert minimum_margin == F(236431, 700) > 0
assert F(27, 10) ** 13 > 200000
assert mp.log(200000) < 13

x = decimal(damping)
quad = mp.quad(lambda t: mp.exp(-4*t*t-x*t), [0, 1, mp.inf])
closed = mp.sqrt(mp.pi) / 4 * mp.exp(x*x/16) * mp.erfc(x/4)
assert abs(quad - closed) < mp.mpf("1e-80")
assert quad > decimal(normalized_lower)
moment_quad = mp.quad(lambda t: t**16 * mp.exp(-t*t-decimal(x_unit)*t),
                      [0, 1, 4, mp.inf])
assert moment_quad > 0
assert abs(decimal(A16) * (2 * quad) + decimal(B16) - moment_quad) < mp.mpf("1e-75")

rows = []
for L in [1, 14, 1800, 10000, 40000, 50000, 55000, 59999, 60000,
          60001, 64000, 100000, 320000, 1000000, 10**9, 10**20]:
    q = F(L + 60000, 1000000)
    adaptive = F(6, L + 60000)
    width = min(F(1, 20000), adaptive)
    old_width = min(F(1, 20000), F(9, 2*(L + 40000)))
    assert width >= old_width
    assert (width == F(1, 20000)) == (L <= 60000)
    if L >= 60000:
        assert width >= F(10, 9) * old_width
        assert width / old_width == F(4, 3) * F(L + 40000, L + 60000)
    row = {
        "logHeight": L,
        "newSimplicityWidth": str(width),
        "previousSimplicityWidth": str(old_width),
        "widthRatio": str(width / old_width),
        "fixedCandidateWidth": "1/20000",
        "entireCandidateStripCeilingPaidHere": L <= 60000,
    }
    if L >= 50000:
        assert q >= F(9, 100)
        assert adaptive * (450000*q) + F(1, 1000) == damping
        source = 67000*q - 4
        cost = 36922*q + F(L, 35) + 57*(F(L, 200000) + 12) + 840
        margin = source - cost
        assert margin == margin_slope*L + margin_constant >= minimum_margin
        row.update({
            "adaptiveDilation": str(q),
            "normalizedDamping": str(damping),
            "completeSourceLower": str(source),
            "rationalCompleteBudgetUpper": str(cost),
            "strictDetectorMargin": str(margin),
        })
    rows.append(row)

result = {
    "classification": "Exact scalar replay of a proved larger simplicity layer",
    "unchangedCeilingTarget": "42/25",
    "simplicityWidth": "min(1/20000,6/(log(abs t+2)+60000))",
    "sourceOfProof": "Exact Gaussian moment recurrence and nonnegative moment 16",
    "allHeightFixedStripCeilingProved": False,
    "simpleZerosExcluded": False,
    "actualPrimeData": False,
    "actualZeroData": False,
    "nativeEntryOrderCertified": False,
    "constants": {
        "normalizedDamping": str(damping),
        "moment16AffineA": str(A16),
        "moment16AffineB": str(B16),
        "exactMoment16UnitLower": str(moment_lower),
        "unitGaussianLower": str(unit_lower),
        "normalizedGaussianLower": str(normalized_lower),
        "physicalSourceSlope": str(source_slope),
        "weightedMultipleSourceSlope": str(weighted_slope),
        "cotangentCostUpper": str(cot_bound),
        "uniformStrictDetectorMargin": str(minimum_margin),
        "marginSlope": str(margin_slope),
        "marginConstant": str(margin_constant),
        "asymptoticWidthRatio": "4/3",
    },
    "independentChecks": {
        "gaussianQuadrature": mp.nstr(quad, 80),
        "quadratureVsClosedDifference": mp.nstr(abs(quad - closed), 20),
        "moment16Quadrature": mp.nstr(moment_quad, 80),
    },
    "rows": rows,
    "limitations": [
        "This is a simplicity layer, not absence of all zeros.",
        "Above log-height 60000 the entire fixed candidate strip remains unpaid.",
        "Detector margins and width ratios are not a Riesz proof completion percentage.",
        "The previous all-family positive-budget no-go is unchanged.",
        "No actual-prime bound or native entry order is certified.",
    ],
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)),
                  "rows": len(rows),
                  "uniformStrictDetectorMargin": str(minimum_margin),
                  "allHeightFixedStripCeilingOpen": True}))
