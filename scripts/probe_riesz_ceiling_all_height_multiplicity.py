#!/usr/bin/env python3
"""Optional exact-scalar replay of the adaptive Gaussian multiplicity payment.

This samples no primes, zeros or carrier arrays. The all-height theorem is
proved in Lean; numerical rows illustrate its arithmetic width and costs.
No wider gate, root build or ordinary CI workflow invokes this probe.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 90
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-all-height-multiplicity/probe.json"


def decimal(x: F) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator


damping = F(1013, 500)
normalized = F(461567, 1875000)
gaussian_slope = 450000 * normalized
weighted_slope = 2 * F(79, 250) * gaussian_slope
conservative_slope = F(70000)
conservative_constant = F(-4)
margin_slope = (conservative_slope - 36922) / 1000000 - F(1, 35) - F(57, 20000)
margin_constant = (conservative_slope - 36922) * F(40000, 1000000) - 4 - 57 * 9 - 840
minimum_margin = 50000 * margin_slope + margin_constant
assert gaussian_slope == F(2769402, 25)
assert weighted_slope == F(218782758, 3125) > conservative_slope
assert -2 * F(79, 250) * 5 > conservative_constant
assert margin_slope == F(2899, 1750000) > 0
assert margin_constant == -F(847, 25)
assert minimum_margin == F(8566, 175) > 0

x = decimal(damping)
quad = mp.quad(lambda t: mp.exp(-4*t*t-x*t), [0, 1, mp.inf])
closed = mp.sqrt(mp.pi) / 4 * mp.exp(x*x/16) * mp.erfc(x/4)
assert abs(quad-closed) < mp.mpf("1e-80")
assert quad > decimal(normalized)
assert mp.log(20000) < 10
assert F(27, 10) ** 10 > 20000

rows = []
for L in [1, 14, 1800, 10000, 40000, 50000, 64000, 100000, 320000,
          1000000, 10**9, 10**20]:
    q = F(L+40000, 1000000)
    adaptive = F(9, 2*(L+40000))
    width = min(F(1, 20000), adaptive)
    old = F(13, 6) * min(F(1, 450000), F(32, 45*L))
    row = {
        "logHeight": L,
        "newSimplicityWidth": str(width),
        "newWidthDecimal": mp.nstr(decimal(width), 65),
        "oldGaussianMultipleZeroWidth": str(old),
        "widthRatioToOldMultiplicityLayer": str(width/old),
        "fixedCandidateWidth": "1/20000",
        "fullFixedStripCeilingPaidHere": L <= 50000,
        "proofUsesPreviousPlateau": L < 50000,
    }
    if L >= 50000:
        assert q >= F(9, 100)
        assert adaptive * (450000*q) + F(1, 1000) == damping
        source = conservative_slope*q + conservative_constant
        rational_cost = 36922*q + F(L, 35) + 57*(F(L, 20000)+9) + 840
        rational_margin = source-rational_cost
        assert rational_margin == margin_slope*L+margin_constant >= minimum_margin
        actual_cost = decimal(36922*q)+mp.mpf(L)/35+57*mp.log(L)+840
        row.update({
            "adaptiveDilation": str(q),
            "exactNormalizedDamping": str(damping),
            "conservativeCompleteSourceLower": str(source),
            "completeRationalBudgetUpper": str(rational_cost),
            "strictRationalMargin": str(rational_margin),
            "rationalSourceMinusLogBudget": mp.nstr(decimal(source)-actual_cost, 65),
        })
    rows.append(row)

result = {
    "classification": "Exact-scalar replay of an all-height actual multiplicity payment",
    "unchangedCeilingTarget": "42/25",
    "provedSimplicityWidth": "min(1/20000,9/(2*(log(abs t+2)+40000)))",
    "provedLogHeightRange": "All heights; no unevaluated threshold",
    "allHeightFixedStripCeilingProved": False,
    "simpleZerosExcluded": False,
    "actualPrimeData": False,
    "actualZeroData": False,
    "nativeCarrierEntryOrderCertified": False,
    "constants": {
        "normalizedGaussianLower": str(normalized),
        "physicalSourceSlope": str(gaussian_slope),
        "weightedMultipleSourceSlope": str(weighted_slope),
        "conservativeSourceSlope": str(conservative_slope),
        "marginSlope": str(margin_slope), "marginConstant": str(margin_constant),
        "uniformStrictDetectorMargin": str(minimum_margin),
        "asymptoticWidthRatioToOldMultiplicityLayer": str(F(1215, 416)),
    },
    "independentChecks": {
        "gaussianQuadrature": mp.nstr(quad, 80),
        "quadratureVsClosedDifference": mp.nstr(abs(quad-closed), 20),
        "log20000": mp.nstr(mp.log(20000), 80),
    },
    "rows": rows,
    "limitations": [
        "The new width concerns multiplicity, not absence of every zero.",
        "Above logarithmic height 50000 it does not cover the entire fixed candidate strip.",
        "Width ratios and detector margins are not Riesz proof completion percentages.",
        "No actual-prime numerical bound or native entry order is certified.",
    ],
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)),
                  "uniformStrictDetectorMargin": str(minimum_margin),
                  "allHeightFixedStripCeilingOpen": True}))
