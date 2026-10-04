#!/usr/bin/env python3
"""Optional joint signed-mode detector, not actual prime/zero data.

Keep the two indices (mode and logged order), integer multiplicities, the
baseline endpoint, and the exact signed complementary population. Verify
the Fejer square identity before scanning wrapped phase geometries.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 115

    def real(x):
        x = F(x)
        return mp.mpf(x.numerator)/x.denominator

    def fmt(x):
        return mp.nstr(x, 100)

    u = real(F(10001, 20000))
    powers = [1100*j for j in range(1, 9)]
    assert sum(F(9-j) for j in range(1, 9)) == 36
    assert sum(F((9-j)*j) for j in range(1, 9)) == 120
    assert 2*36-2*120*F(1, 8) == 42

    def mode(radius, turns, multiplicity=1):
        # turns is the FULL unwrapped turn at the stride. Integer turns
        # cannot be discarded when evaluating the older power4097.
        v = real(radius)*mp.exp(2j*mp.pi*real(turns)/1100)
        w = v**1100
        terms = [(w**j).real for j in range(1, 9)]
        signed = 9+2*sum((9-j)*terms[j-1] for j in range(1, 9))
        prefixes = [sum(w**j for j in range(n+1)) for n in range(9)]
        square = abs(prefixes[8])**2+(1-abs(w)**2)*sum(abs(g)**2 for g in prefixes[:8])
        assert abs(signed-square) < mp.mpf('1e-96')
        excess = signed-9
        coherent = abs(w-1) <= real(F(1, 8))
        assert excess >= -9-mp.mpf('1e-96')
        if coherent:
            assert excess >= 42
        D = u/v
        # Every scanned mode is strictly exposed and lies in the actual
        # nontrivial-strip coordinate domain, but is NOT an actual zero.
        assert abs(D) > u and real(F(1, 2)) < D.real < real(F(3, 2))
        return {'nodeRadius': str(radius), 'stridePhaseFullTurns': str(turns),
                'multiplicity': multiplicity, 'loggedPowers': powers,
                'signedLoggedTerms': list(map(fmt, terms)), 'fejer': fmt(signed),
                'square': fmt(square), 'profileExcess': fmt(excess),
                'tubeDistance': fmt(abs(w-1)), 'coherent': coherent,
                'old4097PowerReal': fmt((v**4097).real),
                'denominatorReal': fmt(D.real), 'denominatorImag': fmt(D.imag),
                'actualZero': False}

    def collect(name, rows, distinct=False):
        # Join the full signed profile before introducing C/O prices.
        profile = sum(r['multiplicity']*mp.mpf(r['profileExcess']) for r in rows)
        old_profile = sum(r['multiplicity']*mp.mpf(r['old4097PowerReal']) for r in rows)
        C = sum(r['multiplicity'] for r in rows if r['coherent'])
        O = sum(r['multiplicity'] for r in rows if not r['coherent'])
        assert C+O == sum(r['multiplicity'] for r in rows)
        assert profile >= 42*C-9*O
        criterion = 3*O <= 14*C+12
        if criterion:
            assert profile >= -36
        if distinct:
            assert len({(r['nodeRadius'], r['stridePhaseFullTurns']) for r in rows}) == len(rows)
        return {'name': name, 'modeRows': rows, 'positions': len(rows),
                'coherentMultiplicity': C, 'otherMultiplicity': O,
                'totalMultiplicity': C+O, 'signedProfile': fmt(profile),
                'old4097Profile': fmt(old_profile),
                'newBalanceLowerExact': str(42*C-9*O),
                'oldSparsePriceExact': str(9*(C+O)),
                'newNetPriceExact': str(9*O-42*C),
                'priceSavingExact': str(51*C),
                'balanceCriterion': criterion,
                'oldMassAtMostFourCriterion': C+O <= 4,
                'oldSingleMomentFloorCriterion': old_profile >= real(F(-1, 5)),
                'profileFloorCriterion': profile >= -36,
                'distinctPositionsReplayed': distinct,
                'actualZeroSamples': 0, 'nativeEntryOrderCertified': False}

    r0 = F(9999, 10000)
    cases = []
    for C, O in [(1, 8), (4, 22), (1, 9), (1, 10), (1000000, 4666670)]:
        cases.append(collect(f'two-position-{C}-{O}',
                             [mode(r0, F(1), C), mode(r0, F(5, 4), O)]))
    dense_rows = ([mode(r0+F(i, 10**9), F(1)+F(i, 10000)) for i in range(100)]+
                  [mode(r0+F(j, 2*10**10), F(5, 4)+F(j, 100000)) for j in range(470)])
    assert sum(r['coherent'] for r in dense_rows) == 100
    cases.append(collect('distinct-position-dense-570', dense_rows, distinct=True))
    assert all(not c['oldMassAtMostFourCriterion'] for c in cases)
    assert all(not c['oldSingleMomentFloorCriterion'] for c in cases)
    assert cases[0]['balanceCriterion'] and not cases[2]['balanceCriterion']
    # The exact signed criterion can be stronger than the coarse C/O debit.
    assert cases[2]['profileFloorCriterion'] and cases[3]['profileFloorCriterion']

    M = 131072
    global_profile = 2*sum((9-j)*(-2+2*M*u**(1100*j)) for j in range(1, 9))
    # The frozen cloud's local cutoff is ||v||>5u/4. Removed modes are
    # bounded only as an already tiny complement, NOT the resonant cloud.
    local_error = 4*M*sum((9-j)*(5*u/4)**(1100*j) for j in range(1, 9))
    assert global_profile+local_error < -37

    data = {'schemaVersion': 1,
            'parameters': {'radiusCeiling': '10001/20000', 'stride': 1100, 'degree': 8,
                           'loggedPowers': powers, 'heightUpper': '10^150',
                           'coherenceTube': '1/8', 'sourceCoefficient': 72,
                           'wholeArithmeticCostUpper': 107, 'profileFloor': '-36',
                           'coherentCredit': 42, 'otherDebit': 9,
                           'balance': '3O <= 14C+12', 'nativeCeiling': '42/25'},
            'bookkeeping': {'modeAndOrderJoinedFirst': True, 'endpoint': 9,
                            'weightSum': 36, 'weightedPowerSum': 120,
                            'profileIsFejerMinusEndpoint': True,
                            'multiplicityCountedOnce': True, 'noComplementDiscarded': True},
            'clusterRows': cases,
            'preservedCloud': {'M': M, 'selectedResidue': -2,
                               'globalProfile': fmt(global_profile),
                               'localCutoff': 'norm(v)>5u/4',
                               'localProfileErrorUpper': fmt(local_error),
                               'stillUnpaid': True, 'actualZero': False},
            'actualPrimeData': False, 'actualZeroData': False,
            'independentArithmeticTheoremUsedByLean': True,
            'conditionalDenseSectorsPaidByLean': True,
            'noBoundOnTotalCompetingMass': True,
            'fullAllHeightCeilingProved': False, 'simpleZeroFloorProved': False,
            'zeroExclusionProved': False, 'nativeEntryOrderCertified': False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2)+'\n')
    print(json.dumps({'clusters': len(cases), 'distinctDensePositions': 570,
                      'signedCreditPerCoherentUnit': 42, 'otherDebitPerUnit': 9,
                      'newDenseBalance': '3O <= 14C+12',
                      'fullAllHeightCeilingProved': False}))


if __name__ == '__main__':
    main()
