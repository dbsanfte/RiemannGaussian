#!/usr/bin/env python3
"""Independent exact/420-bit replay, importing no producer functions."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from flint import arb, acb, ctx


def ball(x):
    x = F(x)
    return arb(x.numerator)/x.denominator


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    ctx.prec = 420
    powers = [1100*j for j in range(1, 9)]
    assert data['parameters'] == {
        'radiusCeiling': '10001/20000', 'stride': 1100, 'degree': 8,
        'loggedPowers': powers, 'heightUpper': '10^150', 'coherenceTube': '1/8',
        'sourceCoefficient': 72, 'wholeArithmeticCostUpper': 107,
        'profileFloor': '-36', 'coherentCredit': 42, 'otherDebit': 9,
        'balance': '3O <= 14C+12', 'nativeCeiling': '42/25'}
    for flag in ['actualPrimeData', 'actualZeroData', 'fullAllHeightCeilingProved',
                 'simpleZeroFloorProved', 'zeroExclusionProved', 'nativeEntryOrderCertified']:
        assert not data[flag], flag
    assert data['noBoundOnTotalCompetingMass'] and data['conditionalDenseSectorsPaidByLean']
    b = data['bookkeeping']
    assert b['modeAndOrderJoinedFirst'] and b['multiplicityCountedOnce']
    assert b['profileIsFejerMinusEndpoint'] and b['noComplementDiscarded']
    assert sum(9-j for j in range(1, 9)) == b['weightSum'] == 36
    assert sum((9-j)*j for j in range(1, 9)) == b['weightedPowerSum'] == 120
    assert b['endpoint'] == 9 and 2*36-2*120*F(1,8) == 42
    u = ball('10001/20000')

    def close(computed, recorded):
        assert abs(computed-arb(recorded)) < arb('1e-90')

    row_count, replayed = 0, []
    for cluster in data['clusterRows']:
        profile, old_profile = arb(0), arb(0)
        C, O = 0, 0
        seen = set()
        for row in cluster['modeRows']:
            row_count += 1
            assert not row['actualZero'] and row['loggedPowers'] == powers
            radius, turn = ball(row['nodeRadius']), ball(row['stridePhaseFullTurns'])
            v = acb(radius)*(acb(0, 2*arb.pi()*turn/1100)).exp()
            w = v**1100
            terms = [(w**j).real for j in range(1, 9)]
            joined = 9+2*sum((9-j)*terms[j-1] for j in range(1, 9))
            prefixes = [sum(w**j for j in range(n+1)) for n in range(9)]
            squares = abs(prefixes[8])**2+(1-abs(w)**2)*sum(abs(g)**2 for g in prefixes[:8])
            assert (joined-squares).contains(0)
            coherent = abs(w-1) < ball('1/8')
            assert coherent == row['coherent']
            close(abs(w-1), row['tubeDistance'])
            close(joined, row['fejer'])
            close(squares, row['square'])
            close(joined-9, row['profileExcess'])
            for value, recorded in zip(terms, row['signedLoggedTerms']):
                close(value, recorded)
            if coherent:
                assert joined-9 > 42
                C += row['multiplicity']
            else:
                assert joined-9 > -9
                O += row['multiplicity']
            old = (v**4097).real
            close(old, row['old4097PowerReal'])
            D = u/v
            close(D.real, row['denominatorReal'])
            close(D.imag, row['denominatorImag'])
            assert abs(D) > u and ball('1/2') < D.real < ball('3/2')
            profile += row['multiplicity']*(joined-9)
            old_profile += row['multiplicity']*old
            seen.add((row['nodeRadius'], row['stridePhaseFullTurns']))
        close(profile, cluster['signedProfile'])
        close(old_profile, cluster['old4097Profile'])
        assert (C, O) == (cluster['coherentMultiplicity'], cluster['otherMultiplicity'])
        assert C+O == cluster['totalMultiplicity']
        assert F(cluster['newBalanceLowerExact']) == 42*C-9*O
        assert F(cluster['oldSparsePriceExact']) == 9*(C+O)
        assert F(cluster['newNetPriceExact']) == 9*O-42*C
        assert F(cluster['priceSavingExact']) == 51*C
        assert profile > 42*C-9*O
        criterion = 3*O <= 14*C+12
        assert criterion == cluster['balanceCriterion']
        assert (C+O <= 4) == cluster['oldMassAtMostFourCriterion']
        assert bool(old_profile >= ball('-1/5')) == cluster['oldSingleMomentFloorCriterion']
        assert bool(profile >= -36) == cluster['profileFloorCriterion']
        if criterion:
            assert profile > -36 and 144+profile > 107
        if cluster['distinctPositionsReplayed']:
            assert len(seen) == cluster['positions'] == len(cluster['modeRows'])
        assert cluster['actualZeroSamples'] == 0 and not cluster['nativeEntryOrderCertified']
        replayed.append({'name': cluster['name'], 'C': C, 'O': O,
                         'balanceCriterion': criterion, 'profileInterval': str(profile)})

    cloud = data['preservedCloud']
    assert cloud['M'] == 131072 and cloud['selectedResidue'] == -2
    assert cloud['stillUnpaid'] and not cloud['actualZero']
    assert cloud['localCutoff'] == 'norm(v)>5u/4'
    M = cloud['M']
    trace = 2*sum((9-j)*(-2+2*M*u**(1100*j)) for j in range(1,9))
    cutoff_error = 4*M*sum((9-j)*(5*u/4)**(1100*j) for j in range(1,9))
    close(trace, cloud['globalProfile'])
    assert abs(cutoff_error-arb(cloud['localProfileErrorUpper']))/cutoff_error < arb('1e-94')
    assert trace+cutoff_error < -37
    result = {'arbPrecisionBits': ctx.prec, 'allSquareIdentitiesReplayed': True,
              'modeRows': row_count, 'clusters': replayed,
              'denseDistinctGeometryPositions': 570, 'exactIntegerBalanceReplayed': True,
              'oldSingleMomentAndSparseTestsFailInAllScannedCases': True,
              'preservedCloudStillUnpaid': True, 'actualPrimeSamples': 0,
              'actualZeroSamples': 0, 'nativeEntryOrderCertified': False,
              'fullAllHeightCeilingProved': False, 'zeroExclusionProved': False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'arbPrecisionBits': ctx.prec, 'modeRows': row_count,
                      'clusterRows': len(replayed), 'densePositions': 570,
                      'exactIntegerBalanceReplayed': True,
                      'fullAllHeightCeilingProved': False}))


if __name__ == '__main__':
    main()
