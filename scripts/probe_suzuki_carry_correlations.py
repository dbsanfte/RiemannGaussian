#!/usr/bin/env python3
"""Optional arithmetic correlation audit, not an interval certificate.

Keep the exact carry incidences, fixed-height phases, prime powers and
integer endpoint gcds. Compare source sensitivity separately from the
strength of the available arithmetic budget.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from probe_suzuki_integer_carry import prime_power_bases


def incidence(N, ds):
    return (2*(N+1)//ds - 2*((N+1)//ds)) - (2*N//ds - 2*(N//ds))


def divisor_phase(a, y):
    """Independent integer factorization replay, including every power."""
    terms = []
    p = 2
    rest = a
    while p*p <= rest:
        power = 1
        while rest % p == 0:
            power *= p
            terms.append(math.log(p)*np.exp(-1j*y*math.log(power)))
            rest //= p
        p += 1
    if rest > 1:
        terms.append(math.log(rest)*np.exp(-1j*y*math.log(rest)))
    return sum(terms, 0j)


def gcd_row(N, M, y, ds, lam):
    raw = complex(np.sum(incidence(N, ds)*incidence(M, ds)*lam*
                         np.exp(-1j*y*np.log(ds.astype(float)))))
    endpoints_N = (2*N+1, 2*N+2, N+1)
    endpoints_M = (2*M+1, 2*M+2, M+1)
    coefficients = (1, 1, -2)
    exact = 0j
    budget = 0.0
    gcds = []
    for a, ca in zip(endpoints_N, coefficients):
        row = []
        for b, cb in zip(endpoints_M, coefficients):
            g = math.gcd(a, b)
            exact += ca*cb*divisor_phase(g, y)
            budget += abs(ca*cb)*math.log(g)
            row.append(g)
        gcds.append(row)
    residual = abs(raw-exact)
    if residual > 5e-12 or abs(raw) > budget+5e-12:
        raise AssertionError('literal correlation/gcd replay failed')
    return {'N': N, 'M': M, 'height': y, 'real': raw.real, 'imag': raw.imag,
            'absolute': abs(raw), 'gcdBudget': budget,
            'gcdMatrix': gcds, 'identityResidualFloating': residual,
            'sharedPrimePowerAtoms': int(np.count_nonzero(incidence(N, ds)*incidence(M, ds)))}


def overlap_row(N, ds, lam):
    c1 = 2*N//ds - 2*(N//ds)
    c2 = 4*N//ds - 2*(2*N//ds)
    if not np.array_equal(c1*c2, (4*N//ds % 4 == 3).astype(int)):
        raise AssertionError('two-scale overlap is not the quotient-3 colour')
    value = float(np.sum(c1*c2*lam))
    mu = float(3*mp.log(2)-mp.pi/2)
    return {'N': N, 'literalOverlap': value, 'continuumLeadingConstant': mu,
            'centeredOverlap': value-mu*N,
            'availableCapacityUpperBound': N*math.log(4),
            'centeredSqrtScaleDiagnostic': (value-mu*N)/math.sqrt(N)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--maximum-n', type=int, default=1 << 18)
    parser.add_argument('--output', type=Path,
                        default=Path('.lake/suzuki-carry-correlation/probe.json'))
    args = parser.parse_args()
    if args.maximum_n < 8192:
        parser.error('maximum-n must be at least 8192')
    mp.mp.dps = 80
    limit = 4*(args.maximum_n+1)
    bases = prime_power_bases(limit)
    ds = np.flatnonzero(bases)
    lam = np.log(bases[ds].astype(np.longdouble))
    sample_N = sorted({1, 2, 3, 256, 640, 1536, 4096, 8192, args.maximum_n})
    rows = []
    for N in sample_N:
        for M in sorted({N+1, N+7, 2*N}):
            for y in [0.0, 60.0]:
                rows.append(gcd_row(N, M, y, ds, lam))
    source_rows = []
    for beta, height, label in [
        (mp.mpf('.9'), mp.mpf(60), 'synthetic density mode'),
        (mp.mpf('.99995'), mp.mpf(60), 'synthetic density mode'),
        (mp.mpf('.5'), mp.zetazero(1).imag, 'known critical zero, numerical control'),
        (mp.mpf('.5'), mp.zetazero(2).imag, 'known critical zero, numerical control'),
    ]:
        s = mp.mpc(beta, height)
        single = (mp.power(2, s)-2)*mp.zeta(s)/s
        overlap = (mp.zeta(s, mp.mpf(3)/4)-mp.zeta(s))/s
        matched = (mp.zeta(beta, mp.mpf(3)/4)-mp.zeta(beta))/beta
        source_rows.append({'kind': label, 'beta': str(beta), 'height': str(height),
                            'singleCarrySymbolAbsolute': mp.nstr(abs(single), 20),
                            'unweightedOverlapSymbolAbsolute': mp.nstr(abs(overlap), 20),
                            'matchedHeightOverlapSource': mp.nstr(matched, 20)})
    report = {
        'scope': 'Optional floating research replay; not a certificate or actual-zero asymptotic',
        'maximumLiteralInteger': limit,
        'fullPrimePowersRetained': True,
        'phaseRetainedBeforeJoining': True,
        'primePowerBasesSHA256': hashlib.sha256(bases.astype('<i8').tobytes()).hexdigest(),
        'gcdCorrelations': rows,
        'overlapRows': [overlap_row(N, ds, lam) for N in sample_N],
        'sourceSensitivity': source_rows,
        'sourceScaleAudit': {
            'linearCapacityBudgetRulesOut_N_power_beta': False,
            'reason': 'For beta<1, N^beta=o(N); a nonblind detector alone is insufficient.',
            'gcdKernelIsFullWeilQuadratic': False,
            'globalSignedOverlapPowerSavingProved': False,
        },
        'outwardRounding': False,
        'newSuzukiFloor': False,
        'rhProved': False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'output': str(args.output), 'correlations': len(rows),
                      'maximumReplayResidual': max(r['identityResidualFloating'] for r in rows),
                      'lastOverlap': report['overlapRows'][-1],
                      'sourceSensitivity': source_rows}, indent=2))


if __name__ == '__main__':
    main()
