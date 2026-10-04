#!/usr/bin/env python3
"""Optional scalar gate for the existing complete Gaussian positive budget.

No primes, zeros, carrier arrays, entry orders or unknown constants are
sampled. The all-order/all-family statements are proved in Lean. Numerical
rows are diagnostics of the unchanged budget and exact cotangent source.
"""
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp

mp.mp.dps = 85
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".lake/riesz-ceiling-gaussian-budget-audit/probe.json"


def real(x: F) -> mp.mpf:
    return mp.mpf(x.numerator) / x.denominator


def text(x: mp.mpf) -> str:
    return mp.nstr(x, 65)


gap = F(1, 20000)
source9 = F(40001)
price9 = F(25, 1023)
source_all = F(280000)
price_all = F(1, 45)
assert F(19, 2**19-2) < gap < F(18, 2**18-2)
assert F(18, 2**18-2) > F(1, 15000)
assert F(96*15000**2, 40500**2) == F(3200, 243) < 14
assert F(28)/(gap+F(1, 15000)) == 240000
assert source9/price9 == F(40921023, 25)
assert source_all/price_all == 12600000
assert 2000000*price9-source9 > 8000
assert 13500000*price_all-source_all == 20000

rows = []
checks = []
for dilation in [F(9, 100), F(1), F(10), F(100), F(1000)]:
    x = F(1, 450000000)/dilation
    B = F(4, 450000**2)/(dilation*dilation)
    damping = x+gap
    dm, bm = real(damping), real(B)
    # Scaling by damping avoids enormous exp/erfc factors at small B.
    G = mp.quad(lambda v: mp.exp(-v-bm*v*v/(dm*dm)), [0, 1, mp.inf])/dm
    closed = mp.sqrt(mp.pi)/(2*mp.sqrt(bm))*mp.exp(dm*dm/(4*bm))*mp.erfc(dm/(2*mp.sqrt(bm)))
    assert abs(G-closed) < mp.mpf("1e-72")
    assert G <= 1/dm <= 20000
    checks.append({"dilation": str(dilation), "halfGaussian": text(G),
                   "quadratureVsClosedDifference": text(abs(G-closed))})
    for k in range(3, 17):
        alpha = F(1, 2**(k+2)-2)
        delta = (k+2)*alpha
        eta = delta+x
        factor = 24*B/(eta*eta)
        assert gap < delta and x <= delta/4
        assert eta >= F(1, 15000) and factor <= 14
        assert alpha/(2*eta) >= price_all
        f = mp.pi/(2*real(eta))
        cot_correction = f/mp.tan(f*dm)-1/dm
        reserve = real(factor)*2/(dm+real(eta))
        exact_source = 2*(G+cot_correction)+reserve
        lower_source = 2*(G-mp.pi**2*dm/(8*real(eta)**2))+reserve
        envelope = 2*G+reserve
        assert cot_correction <= 0 and lower_source <= exact_source <= envelope <= real(source_all)
        if k == 9:
            assert lower_source <= real(source9)
            assert alpha/(2*eta) >= price9
        for L in [50000, 1000000, 2000000, 12600000, 13500000]:
            literal_price_lower = alpha*L/(2*eta)
            rows.append({
                "order": k, "dilation": str(dilation), "logHeight": L,
                "exactDelta": str(delta), "halfWidth": str(eta),
                "exactCotangentSourcePerFirstCoefficient": text(exact_source),
                "earlierLowerCertificatePerFirstCoefficient": text(lower_source),
                "gaussianPlusReserveEnvelope": text(envelope),
                "literalPositiveBudgetLowerPerNonconstantMass": str(literal_price_lower),
                "sourceMinusBudgetLowerAtFirstToMassRatioOne": text(exact_source-real(literal_price_lower)),
                "allOrderNoSurplusGateApplies": L >= 12600000,
                "allOrderMargin20000GateApplies": L >= 13500000,
            })

result = {
    "classification": "Scalar replay of a proved complete-positive-budget method limit",
    "fixedCandidateGap": str(gap), "unchangedCeilingTarget": "42/25",
    "actualPrimeData": False, "actualZeroData": False,
    "newArithmeticCeilingCredit": 0, "allHeightFixedStripCeilingProved": False,
    "nativeCarrierEntryOrderCertified": False,
    "scope": {
        "dilationFamily": "q>=9/100; B=4/(450000*q)^2, x=1/(450000000*q)",
        "coefficientFamilies": "all summable nonnegative families; first coefficient <= nonconstant mass",
        "frequencyFamilies": "omega(n)>=1 for n!=0",
        "reachingDerivativeOrders": "k<=16; existing Gaussian source theorem uses k>=3",
        "exactCotangentRetainedInAllOrderGate": True,
        "signedExactBudgetRuledOut": False,
    },
    "exactConstants": {
        "order9SourceCertificateUpper": str(source9), "order9LiteralPriceSlope": str(price9),
        "order9NecessaryLogHeightCeiling": str(source9/price9),
        "allOrderSourceUpper": str(source_all), "allOrderLiteralPriceSlope": str(price_all),
        "allOrderNecessaryLogHeightCeiling": str(source_all/price_all),
        "allOrderDominanceLogHeight": 13500000, "allOrderDominanceMargin": "20000*mass(a)",
    },
    "independentQuadratureChecks": checks, "rows": rows,
    "limitations": [
        "Bounds concern the stated complete positive budget, not the signed clipped mean.",
        "The source is tested at the fixed boundary with multiplicity two; no such zero is asserted to exist.",
        "Necessary height ceilings do not assert any valid surplus below them.",
        "The all-height moving simplicity layer and all earlier payments remain valid.",
        "No new zero exclusion or bound on the signed Riesz carrier follows.",
    ],
}
OUT.parent.mkdir(parents=True, exist_ok=True)
OUT.write_text(json.dumps(result, indent=2)+"\n")
print(json.dumps({"output": str(OUT.relative_to(ROOT)), "rows": len(rows),
                  "allOrderNecessaryLogHeightCeiling": 12600000,
                  "newArithmeticCeilingCredit": 0}))
