#!/usr/bin/env python3
"""Optional rate diagnostic for the proved whole-core owner payment.

This evaluates tail suprema and the fixed source rate, not an arithmetic
population, signed floor, effective start, or summable reference constant.
It is outside ordinary builds and CI.
"""

import json
import math

from scipy.special import logsumexp
from scipy.stats import binom


def main():
    radius = 10001/20000
    sigma = 1+1/1048576
    tilt = 103/100
    cofactor_share = 499/1250
    upper_log = math.log1p(cofactor_share*(tilt-1))-(13/32)*math.log(tilt)
    source_log = math.log(radius/(1.5-sigma))
    assert upper_log <= -1033/10000000
    assert upper_log+source_log < -1/1000000
    samples = []
    for n in (320, 640, 1536, 4096, 8192, 100000):
        # Separate endpoints bound the two tails; they are not one label.
        upper = binom.logsf(13*n//32, n+1, cofactor_share)
        lower = binom.logcdf(n//5+1, n+1, 7/25)
        combined = float(logsumexp([upper, lower]))
        samples.append(dict(
            N=n,
            logTailSuprema=combined if math.isfinite(combined) else None,
            numericalUnderflow=not math.isfinite(combined),
            provedLogMissingMassBound=math.log(9/4)-1033*n/10000000,
            provedLogAllowanceDividedByReferenceMass=
                math.log((9/4)*radius)-n/1000000,
        ))
    print(json.dumps(dict(
        diagnosticOnly=True, noArithmeticPopulationEvaluated=True,
        ownerShareThreshold=751/1250, previousThreshold=601/1000,
        upperTilt=tilt, sourceGrowthLog=source_log,
        tiltedSourceDecayMargin=-(upper_log+source_log),
        provedDecayRate=1/1000000,
        arithmeticReferenceMassEvaluated=False,
        effectiveStartCertified=False, wholeFloorCertified=False,
        samples=samples,
    ), indent=2))


if __name__ == '__main__':
    main()
