#!/usr/bin/env python3
"""Independent scalar/incomplete-gamma replay of the optional integer gate.

This does not re-enumerate all floating floor decisions or certify an
infinite binary witness. It rejects upgrades to ordinary-prime coverage or
a numerical ceiling claim.
"""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mp.mp.dps = 85
    p = json.loads(args.input.read_text())
    assert p['allComputedWeightsZeroOrOne'] and p['cumulativeCountsTelescope']
    assert p['controlParameters']['outsideTargetRadius']
    assert p['integerAtoms'] == 1045597 and p['selectedUnitAtoms'] == 81554
    for flag in ['allActualPrimesUsed', 'primeSupportClaimed',
                 'infiniteBinaryCounterexampleLeanFormalized',
                 'allFloorDecisionsBallCertified', 'independentCeilingProved',
                 'zeroExclusionProved', 'nativeEntryOrderCertified']:
        assert p[flag] is False, flag
    assert p['ceilingCredit'] == 0
    assert len(p['criticalFloorReplays']) == 32
    assert all(r['floorAgrees'] for r in p['criticalFloorReplays'])

    r = F(10001, 20000)/F(3, 2)
    assert F(p['targetScalarRatio']) == r == F(10001, 30000) < F(1, 2)
    u = mp.mpf(10001)/20000
    c = mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))-mp.log(mp.mpf(19)/13)
    assert abs(mp.mpf(p['existingContinuousDoubleSource'])-(-2+4*c)) < mp.mpf('1e-68')
    for row in p['targetScalarRows']:
        N = row['order']
        rr = mp.mpf(r.numerator)/r.denominator
        value = mp.log10(2*(1+mp.sqrt(mp.mpf('1.5')**2+54**2)
                           /mp.mpf('1.5'))*(N+1)*rr**(N+1))
        assert abs(mp.mpf(row['log10OfDerivedInfiniteRoundingPrice'])-value) < mp.mpf('1e-37')
        assert row['literalTargetPrimeSumEvaluated'] is False

    assert [row['order'] for row in p['finiteRows']] == [0, 1, 2, 4, 8, 12, 16]
    u0, y, B, M = mp.mpf(3)/4, 54, 8, 2**20
    T = mp.log(M)
    for row in p['finiteRows']:
        k = row['order']

        def integral(z):
            return mp.gammainc(k+1, z*B, z*T)/(mp.factorial(k)*z**(k+1))

        continuous = u0**(k+1)*(integral(mp.mpc('.5', y))
                               -2*integral(u0)-2*integral(mp.mpc(u0, 2*y)))
        assert abs(mp.mpc(*row['finiteContinuousMoment'])-continuous) < mp.mpf('1e-15')
        atom = mp.mpc(*row['finiteUnitIntegerMoment'])
        # The producer exports 40 significant digits, not all 85 working digits.
        assert abs(mp.mpf(row['roundingError'])-abs(atom-continuous)) < mp.mpf('1e-40')
        price = 2*(k+1)*(1+abs(mp.mpc('1.5', y))/mp.mpf('1.5'))*(u0/mp.mpf('1.5'))**(k+1)
        endpoint = u0**(k+1)*T**(k+1)/mp.factorial(k)*M**(-mp.mpc('1.5', y))
        price += 2*abs(endpoint)
        assert abs(mp.mpf(row['statedFiniteAbelPrice'])-price) < mp.mpf('1e-36')
        assert abs(atom-continuous) <= price

    result = {'independentIncompleteGammaMomentRows': len(p['finiteRows']),
              'independentTargetScalarPriceRows': len(p['targetScalarRows']),
              'allFloorDecisionsIndependentlyReplayed': False,
              'infiniteBinaryWitnessCertified': False,
              'actualPrimeCeilingCredit': 0}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
