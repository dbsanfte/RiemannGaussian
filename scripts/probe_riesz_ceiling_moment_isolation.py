#!/usr/bin/env python3
"""Optional scalar exploration of the complete-moment ceiling test.

This samples neither primes nor zeros. Separation radii are explicit
hypotheses, never measured or supplied by exposure alone. The exact block
certificates mirror the proved Lean finite-order result; the minimising
orders below are exploratory grid choices, not optimality certificates.
Outside ordinary builds and CI.
"""
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 100
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-moment-isolation/probe.json"
U = F(10001, 20000)
HEIGHT = 10**150
N = 4096


def decimal(x):
    if isinstance(x, F):
        return mp.mpf(x.numerator) / x.denominator
    return mp.mpf(x)


def components(radius, order, height=HEIGHT):
    u, r, h = decimal(U), decimal(radius), decimal(height)
    return {
        "realAxisPole": (2*u)**(order+1),
        "competingActualZeros": (h+11)*(u/r)**(order+1),
        "zetaPoleAtHeight": u**(order+1),
        "completeResidualIncludingRealAxis":
            160*u*(h+4)*(order+1)*(10*u/7)**order,
        "canonicalReflectedChannels": (h+11)*(4*u/3)**(order+1),
    }


blocks = [
    ("realAxisGrowth", F(10001, 10000), F(129, 128)),
    ("competingDecay", F(10001, 11000), F(1, 400)),
    ("heightPoleDecay", U, F(1, 10**18)),
    ("analyticDecay", F(10001, 14000), F(1, 10**9)),
    ("reflectedDecay", F(10001, 15000), F(1, 10**10)),
]
certificates = []
for name, base, upper in blocks:
    assert base**64 <= upper
    certificates.append({"name": name, "base": str(base), "power": 64,
                         "upper": str(upper),
                         "numericalValue": mp.nstr(decimal(base)**64, 90),
                         "exactRationalComparison": True})

coarse = [
    U*2*F(129, 128)**64,
    (HEIGHT+11)*F(1, 400)**64,
    F(1, 10**18)**64,
    160*U*(HEIGHT+4)*4097*F(1, 10**9)**64,
    (HEIGHT+11)*F(1, 10**10)**64,
]
assert coarse[0] < F(7, 4)
assert all(term < F(1, 1000) for term in coarse[1:])
assert sum(coarse) < 2
fixed = components(F(11, 20), N)
assert sum(fixed.values()) < 2

# Recurrence rather than thousands of fresh high powers. Report only the
# sampled minimum and the range used. No continuous-optimiser claim.
rows = []
for radius in [F(51, 100), F(21, 40), F(27, 50), F(11, 20), F(3, 5), F(7, 10)]:
    u, r, h = decimal(U), decimal(radius), mp.mpf(HEIGHT)
    main, comp, pole, reflected, analytic = 1, h+11, 1, h+11, 160*u*(h+4)
    best = (mp.inf, None)
    for order in range(1, 6900):
        if order == 1:
            vals = components(radius, order)
            main = vals["realAxisPole"]
            comp = vals["competingActualZeros"]
            pole = vals["zetaPoleAtHeight"]
            reflected = vals["canonicalReflectedChannels"]
            analytic = vals["completeResidualIncludingRealAxis"]
        else:
            main *= 2*u
            comp *= u/r
            pole *= u
            reflected *= 4*u/3
            analytic *= (10*u/7)*mp.mpf(order+1)/order
        total = main+comp+pole+analytic+reflected
        if total < best[0]:
            best = total, order
    rows.append({"hypotheticalCompetingRadius": str(radius),
                 "exploratoryOrders": [1, 6899],
                 "sampledBestOrder": best[1],
                 "sampledTestUpper": mp.nstr(best[0], 90),
                 "sampledTestBelowTwo": best[0] < 2,
                 "noGlobalOptimumClaim": True})

result = {
    "classification": "Scalar replay of an actual arithmetic isolation-sector payment",
    "unchangedCeilingTarget": "42/25",
    "parameters": {"radiusCeiling": str(U), "competingRadius": "11/20",
                   "logHeightCeiling": str(HEIGHT), "momentOrder": N,
                   "heightLog": "log(abs(y)+22)", "realAxisLogUpper": 4},
    "exactBlockCertificates": certificates,
    "certifiedCoarseTestUpper": mp.nstr(decimal(sum(coarse)), 90),
    "leanTestThreshold": "7/4+4/1000<9/5<2",
    "fixedTestComponents": {key: mp.nstr(value, 90) for key, value in fixed.items()},
    "fixedTestUpper": mp.nstr(sum(fixed.values()), 90),
    "provedSignedCounterweightThreshold": "-1/5",
    "signedCounterweightNeedsCompetingGap": False,
    "numericalCounterweightRequiredForDoubleSource": mp.nstr(
        2-sum(value for key, value in fixed.items() if key != "competingActualZeros"), 90),
    "exploratoryRadiusRows": rows,
    "actualPrimeData": False,
    "actualZeroData": False,
    "uniformExposedGapAssumed": False,
    "competingGapIsExtraHypothesis": True,
    "isolatedSectorCeilingLeanProved": True,
    "allHeightFixedStripCeilingProved": False,
    "simpleZeroExclusionProved": False,
    "nativeEntryOrderCertified": False,
    "remainingCluster": {"competingCentreDistanceAtMost": "11/20",
                         "realPartAtLeast": "19/20", "ordinateGapBelow": "1/4"},
    "limitations": [
        "The displayed height bound is finite, even though it is very large.",
        "Exposure supplies a gap greater than u, not the required 11/20.",
        "Only multiple isolated zeros are excluded; simple zeros are not.",
        "The general finite-order inequality, not a new carrier, is being sampled.",
        "A threshold below two is a multiplicity test, not a Riesz progress percentage.",
    ],
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)), "fixedTestUpper": result["fixedTestUpper"],
                  "exactBlockCertificates": len(certificates), "exploratoryRadiusRows": len(rows),
                  "fullCeilingStillOpen": True}))
