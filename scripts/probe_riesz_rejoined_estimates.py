#!/usr/bin/env python3
"""Optional audit of the five remaining floor estimates.

The debit table evaluates the explicit lower bound already proved in
ZetaRieszGlobalDebitAudit, not the signed carrier. The multiscale examples
are continuous prime-log models, not actual prime labels. They deliberately
test whether many occupied bins force opposite active Mobius parities.
Neither part certifies the numerical floor. Never run this in ordinary CI.
"""

import json
import math

import mpmath as mp

from probe_riesz_few_bin_cover import grid_subset_counts, tent
from probe_riesz_dense_count_cover import dyadic_scale

mp.mp.dps = 100
U = mp.mpf(10001)/20000


def source_debit_table():
    # Exact functional lower bound in supply_tailDebit_lower. The supply
    # constant c cancels; y=54 is one illustrative fixed height.
    height = 54
    coefficient = 128*U*mp.e/(3*(math.floor(2*height)+1))
    return [dict(
        N=n, fixedHeight=height,
        sourceTailDebitLowerLog10=float(
            (mp.log(coefficient)+n*mp.log(2*U)-5*mp.log(n+1))/mp.log(10)),
        carrierValueComputed=False,
    ) for n in (4000, 10000, 100000, 500000, 1000000, 10000000)]


def optimistic_packing_envelope_table():
    # Exact count identity: omega(B)=omega(n)-3. Every currently remaining
    # rank is STRICTLY below5*log(N+1)-1. Use the largest allowed rank to
    # give packing its strongest possible saving on this range. This is
    # still a COMMON POSITIVE PERIOD ENVELOPE calculation, NOT a lower
    # bound for the actual separated population or for the signed carrier.
    rows = []
    for n in (100000, 500000, 1000000, 10000000, 100000000):
        rank = int(mp.ceil(5*mp.log(n+1)-1))-1
        assert rank >= 53 and rank < 5*mp.log(n+1)-1
        period_log = (mp.log(U/3)-1+n*mp.log(2*U)-mp.log(n+1))
        price_log = period_log-mp.log(mp.mpf(2)**rank-1)
        rows.append(dict(
            N=n, largestAllowedBackgroundRank=rank,
            currentLogCountRangeNonempty=True,
            sourcePackingPeriodEnvelopeLowerLog10=float(price_log/mp.log(10)),
            actualSeparatedPopulationCostComputed=False,
            signedCarrierValueComputed=False,
        ))
    return rows


def multiscale_layer(ratio, count):
    # All background log-grid indices are odd, at very different scales.
    # Consequently every divisor at grid index j has parity (-1)^j.
    # Small independent perturbations preserve this parity on a strict
    # isolated active cell; exact equality of distinct divisor logs is
    # NOT required for the one-parity conclusion.
    odd = []
    for i in range(count):
        candidate = 2*round(3*ratio**i)+1
        odd.append(max(candidate, odd[-1]+2 if odd else 1))
    assert len(odd) == len(set(odd)) and all(x % 2 for x in odd)
    signed, unsigned = grid_subset_counts(odd)
    assert all(sg == (-1)**j*un for j, (sg, un) in enumerate(zip(signed, unsigned)))
    unit, scale = mp.mpf(32), mp.mpf(10)**6
    a, b = mp.mpf(3), mp.mpf(6)
    logs = [a, b, *(unit*x for x in odd)]
    cofactor = sum(logs)*scale
    rows = []
    directions = set()
    for i in range(10001):
        share = mp.mpf('0.54')+mp.mpf(i)/500000
        total = cofactor/(1-share)
        order = total/mp.mpf('1.99')
        length = -2*order*mp.log(U)-2*mp.log(order+1)
        first = (total-length)/scale
        second = (cofactor-length)/scale
        assert second < 0
        j = int(mp.floor(first/unit))
        offset = first-unit*j
        if not (2 < offset < 7 and 0 <= j < len(unsigned) and unsigned[j]):
            continue
        head = max(mp.mpf(5000), 32*mp.log(order+1))
        bins = {dyadic_scale(x*scale, head) for x in logs if head < x*scale}
        ceiling = int(mp.floor(mp.log(order+1)/16))
        assert count+3 >= 56 and count+3 < 5*mp.log(order+1)+2
        assert len(bins) > ceiling
        assert total*share > max(logs)*scale
        value = tent(offset, a, b)
        response = (-1)**len(logs)*signed[j]*value*scale
        phase = mp.exp(-mp.j*54*total)
        signed_real = (phase*response).real
        direction = 'negative' if signed_real < 0 else 'positive'
        if direction in directions or abs(phase.real) < mp.mpf('0.2'):
            continue
        directions.add(direction)
        rows.append(dict(
            continuousLogModel=True, actualPrimeLabel=False,
            exactMovingIntegerLength=False, literalPacketCertified=False,
            nominalBackgroundCount=count, totalPrimeCount=count+3,
            occupiedBinCount=len(bins), paidBinCeiling=ceiling,
            modelCountAndBinInequalitiesSatisfied=True,
            modelLogN=float(mp.log(order)), ownerShare=float(share),
            activeBackgroundGridIndex=j,
            activeBackgroundDivisorCount=unsigned[j],
            activeBackgroundParity='even' if j % 2 == 0 else 'odd',
            activeTentOffset=float(offset), twoHingeSignedResponse=float(response),
            signedToUnsignedRatio=1,
            commonPhaseReal=float(phase.real),
            commonPhaseWeightedResponseReal=float(signed_real),
            sourceScaledFactorialAndAllocationNotEstimated=True,
            independentLogPerturbationBudgetInUnscaledLogUnits=float(mp.mpf('0.001')/count),
            perturbationBudgetIsModelOnly=True,
            populationWeightNotEstimated=True,
        ))
        if len(rows) == 2:
            return rows
    raise AssertionError('No strict active cell found')


def main():
    print(json.dumps(dict(
        diagnosticOnly=True, ordinaryBuildOrCI=False,
        numericalFloorCertified=False,
        sourceGrowthRate=float(mp.log(2*U)),
        separatedPackingFactorAtCount56=float(1/mp.mpf(2)**53),
        exactLeanPackingFactorAtCount56=float(1/(mp.mpf(2)**53-1)),
        supplyTailDebitLowerBounds=source_debit_table(),
        strongestLogRankPackingPeriodEnvelope=optimistic_packing_envelope_table(),
        manyBinOneParityModels=multiscale_layer(1.12, 56),
        conclusions=[
            'A relatively vanishing debit need not be small at source scale.',
            'The packing theorem reduces the actual separated coefficient, not its population mass.',
            'Packing against the common positive period envelope still grows, even at the largest remaining rank.',
            'Many occupied prime-log bins do not force both parities in an active window in these models.',
            'All-count local pairing does not close the global signed prime-period estimate.',
        ],
        limitations=[
            'The modular examples are not actual prime labels and do not refute a whole-carrier floor.',
            'No sum over actual prime populations, transport coverage or weighted unmatched mass is computed.',
            'The fixed-period phase and source lower bound are distinct diagnostics.',
        ],
    ), indent=2, allow_nan=False))


if __name__ == '__main__':
    main()
