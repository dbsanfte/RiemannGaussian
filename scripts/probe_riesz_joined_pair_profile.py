#!/usr/bin/env python3
"""Optional joined-coefficient exploration, outside ordinary builds/CI.

This is a profile grid, not actual prime counting, a zero ordinate test,
a cofinal certificate or a value in units of the 399/5000 floor. The
independent Lean sign inequalities do not depend on these floating results.
"""
import argparse
import json
import math
from pathlib import Path

import mpmath as mp
from scipy.stats import binom


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 80
    rows = []
    for N in (65536, 196608, 917504):
        K = 13*N//32
        for num, den in ((1, 2), (10001, 20000)):
            u = mp.mpf(num)/den
            # Certified literal enclosure from the previous length audit:
            # L0 <= length <= L0+4*(N+1)*u**N. Use L0 for exploration.
            L0 = -2*N*mp.log(u)-2*mp.log(N+1)
            log_width = mp.log(4)+mp.log(N+1)+N*mp.log(u)
            for tnum, tden in ((39, 20), (2, 1), (203, 100)):
                T = N*tnum/tden
                radial_ratio = T/float(L0)
                for qnum, qden in ((1, 2), (13, 25), (5, 8), (11, 16), (3, 4)):
                    q = qnum/qden
                    Fx = float(binom.cdf(K, N+1, q))
                    Fz = float(binom.cdf(K, N+1, 1-q))
                    raw_prefix = 1-radial_ratio-(1-radial_ratio*q)*Fz-(1-radial_ratio*(1-q))*Fx
                    selberg_credit = 2*q*(1-q)
                    joined = raw_prefix+selberg_credit
                    assert math.isfinite(joined)
                    rows.append(dict(
                        N=N, radius=f'{num}/{den}', totalLogSlope=f'{tnum}/{tden}',
                        largestLogShare=f'{qnum}/{qden}', literalOrderCutoff=K,
                        lengthLowerEndpoint=mp.nstr(L0, 65),
                        logLiteralEnclosureWidth=mp.nstr(log_width, 65),
                        exactPrefixEvaluatedNumerically=Fx,
                        exactCofactorPrefixEvaluatedNumerically=Fz,
                        rawPrefixNormalizedCoefficient=raw_prefix,
                        fullSelbergNormalizedCoefficient=selberg_credit,
                        joinedNormalizedCoefficient=joined))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(dict(
        classification='Exploratory coefficient profile; independent Lean sign cover',
        actualPrimePopulation=False, actualZeroHeight=False, phaseOrCountDensityEstimated=False,
        literalLengthEnclosureRetained=True, factorialFloorRetained=True,
        mathematicalCertificate=False, cofinalFloorCredit=0, cases=len(rows), rows=rows), indent=2)+'\n')
    balanced = [r['joinedNormalizedCoefficient'] for r in rows
                if r['largestLogShare'] in ('1/2', '13/25')]
    owner = [r['joinedNormalizedCoefficient'] for r in rows
             if r['largestLogShare'] in ('5/8', '11/16')]
    print(json.dumps(dict(cases=len(rows), balancedMinimum=min(balanced),
                         ownerMaximum=max(owner), floorCredit=0)))


if __name__ == '__main__':
    main()
