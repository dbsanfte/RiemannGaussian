#!/usr/bin/env python3
"""Optional scalar discovery/replay for the proved Gaussian multiplicity payment.

No prime, zeta-zero or carrier population is sampled. Exact rational arithmetic
replays the proof's tangent/budget constants; quadrature independently checks
the scalar Gaussian enclosure. Lean, not this probe, proves the height interval.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 80
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-gaussian-multiplicity/probe.json"


def decimal(x: F) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator


q = F(9, 100)
width = 1 / (450000 * q)
shift = width / 1000
gap = F(1, 20000)
damping = gap / width + F(1, 1000)
tangent_at = F(1, 5)
sqrt_lower = F(443, 1000)
exp_lower = F(2, 3)
normalized_lower = exp_lower * ((1 + damping * tangent_at) * sqrt_lower - damping / 8)
physical_lower = normalized_lower / width
multiple_source = F(79, 250) * 2 * (physical_lower - 5)
rational_cost = 36922 * q + F(50000, 35) + 57 * 11 + 840
strict_margin = multiple_source - rational_cost
assert normalized_lower == F(461567, 1875000)
assert physical_lower == F(12462309, 1250)
assert multiple_source == F(984028661, 156250)
assert strict_margin == F(43330001, 546875) > 0

x = decimal(damping)
gaussian_closed = mp.sqrt(mp.pi) / 4 * mp.exp(x*x/16) * mp.erfc(x/4)
gaussian_quad = mp.quad(lambda t: mp.exp(-4*t*t-x*t), [0, 1, mp.inf])
assert abs(gaussian_closed-gaussian_quad) < mp.mpf("1e-70")
assert gaussian_quad > decimal(normalized_lower)
assert mp.exp(-x/5) > decimal(exp_lower)

rows = []
for L in [1, 14, 64, 1800, 6000, 10000, 20000, 40000, 50000, 52000, 55000]:
    cost = decimal(36922*q) + mp.mpf(L)/35 + 57*mp.log(L) + 840
    rows.append({
        "logHeight": L,
        "costExpression": mp.nstr(cost, 60),
        "rationalSourceMinusCost": mp.nstr(decimal(multiple_source)-cost, 60),
        "insideProvedHeightRange": 1 <= L <= 50000,
    })

result = {
    "classification": "Replay of proved scalar Gaussian multiplicity constants, not prime sampling",
    "unchangedCeilingTarget": "42/25",
    "provedCandidateStrip": "Re rho >= 19999/20000",
    "provedLogHeightRange": "log(abs(Im rho)+2) <= 50000",
    "newAllHeightCeiling": False,
    "newAllZeroFreeRegion": False,
    "multipleZerosExcludedInStatedRange": True,
    "simpleZerosExcluded": False,
    "actualPrimeData": False,
    "actualZeroData": False,
    "entryOrderCertified": False,
    "exactConstants": {
        "dilation": str(q), "normalizedDamping": str(damping),
        "tangentPoint": str(tangent_at), "normalizedGaussianLower": str(normalized_lower),
        "physicalGaussianLower": str(physical_lower), "multipleSourceLower": str(multiple_source),
        "completeRationalBudgetAtCeiling": str(rational_cost), "strictMargin": str(strict_margin),
    },
    "scalarChecks": {
        "normalizedGaussianQuadrature": mp.nstr(gaussian_quad, 70),
        "quadratureVsClosedAbsoluteDifference": mp.nstr(abs(gaussian_closed-gaussian_quad), 15),
        "expAtTangent": mp.nstr(mp.exp(-x/5), 70),
        "log50000": mp.nstr(mp.log(50000), 70),
    },
    "rows": rows,
    "warning": "Rows beyond 50000 are exploration only. This probe does not certify a maximal height or native carrier entry order.",
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)), "exactMargin": str(strict_margin),
                  "rationalSourceLower": str(multiple_source), "allHeightCeilingOpen": True}))
