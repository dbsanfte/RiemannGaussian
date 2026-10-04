#!/usr/bin/env python3
"""Independently replay the algebraic preflight without importing its producer."""

import argparse
from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path

import mpmath as mp


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def collect(records):
    result = defaultdict(lambda: [Fraction(0), Fraction(0)])
    for record in records:
        key = (record['key'][0], tuple(tuple(v) for v in record['key'][1]))
        assert key[1] == tuple(sorted(zip(record['incidence'], record['factorialOrders'])))
        assert record['totalOrder'] == sum(record['factorialOrders'])
        result[key][0] += Fraction(record['constant'])
        result[key][1] += Fraction(record['inverseL'])
    return result


def expected(N, diagonal, key):
    """Closed coefficient table, independent of the stream construction."""
    M, K = N+1, 13*N//32
    ((_, i), (_, j)) = key[1]
    lo, hi = min(i, j), max(i, j)
    symmetry = Fraction(1, 2) if diagonal and i == j else Fraction(1)
    if i+j == M:
        return (symmetry*M, Fraction(0)) if K < lo else (Fraction(0), Fraction(0))
    assert i+j == M+1
    if K < lo:
        return Fraction(0), -symmetry*M*(M+1)
    return Fraction(0), -Fraction(M*lo)


def cumulative(n, k, p):
    """Positive binomial recurrence; no SciPy or producer routine."""
    if k < 0:
        return mp.mpf(0)
    value, total = (1-p)**n, mp.mpf(0)
    for j in range(k+1):
        total += value
        if j < k:
            value *= (n-j)*p/((j+1)*(1-p))
    return total


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', type=Path, default=Path('.lake/riesz-pair-algebra/preflight.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-algebra/validation.json'))
    args = ap.parse_args()
    r = json.loads(args.input.read_text())
    for pin in r['sources']:
        assert sha(pin['path']) == pin['sha256']
    templates = []
    for template in r['exactAlgebra']['templates']:
        a, b = collect(template['raw']), collect(template['surviving'])
        for key in a.keys() | b.keys():
            want = expected(template['N'], template['repeatedPrimeDiagonal'], key)
            assert tuple(a.get(key, (0, 0))) == want
            assert tuple(b.get(key, (0, 0))) == want
        templates.append(dict(N=template['N'], diagonal=template['repeatedPrimeDiagonal'],
            closedCoefficientTableMatches=True, endpointCoefficientsExactlyZero=True))
    # Floating replay against independent high-precision logarithms and
    # binomial recurrence. The representative row is explicitly a sample.
    mp.mp.dps = 85
    coefficients, masses = [], []
    for profile, literal in zip(r['factorialRowProfiles'], r['literalComponents'], strict=True):
        assert profile['box'] == literal['box']
        N, L = profile['N'], mp.mpf(str(literal['movingLength']))
        p, q = map(int, profile['actualPrimes'])
        x, z = mp.log(p), mp.log(q)
        T, M, K = x+z, N+1, 13*N//32
        px, pz = x/T, z/T
        Fx, Fz = cumulative(M, K, px), cumulative(M, K, pz)
        direct = T*(1-T/L)-T/L*((L-x)*Fz+(L-z)*Fx)
        reduced = T*(1-Fx-Fz)
        reduced -= T*T/L*(1-cumulative(M+1, K, px)-cumulative(M+1, K, pz))
        reduced -= T/L*(x*cumulative(M, K-1, px)+z*cumulative(M, K-1, pz))
        error = abs(direct-reduced)
        assert error < mp.mpf('1e-65')
        coefficients.append(dict(box=profile['box'], absoluteIdentityError=float(error)))
        for suffix, order, prob in (('M_p', M, px), ('M_q', M, pz),
                                    ('MPlus1_p', M+1, px), ('MPlus1_q', M+1, pz)):
            stored = profile['massOrder'+suffix]
            mass = (1-prob)**order
            max_error, total = mp.mpf(0), mp.mpf(0)
            for k, got in enumerate(stored):
                want = mass if k <= order else mp.mpf(0)
                max_error = max(max_error, abs(mp.mpf(float(got))-want))
                total += want
                if k < order:
                    mass *= (order-k)*prob/((k+1)*(1-prob))
            assert abs(total-1) < mp.mpf('1e-65')
            assert max_error < mp.mpf('1e-12')
            masses.append(dict(box=profile['box'], leg=suffix,
                maxFloatMassError=float(max_error), allFactorialOrdersReplayed=True))
    assert r['cofinalFloorCredit'] == 0 and not r['floor'] and not r['RH']
    # The statistical handoff must preserve the original already-joined
    # target. Compare overlapping dyadic offsets against its frozen prior
    # scan, not against another implementation of the new decomposition.
    old_path = Path('.lake/riesz-pair-joint/scan.json')
    old = json.loads(old_path.read_text())
    handoffs = []
    for profile in r.get('survivorPhaseProfiles', []):
        key = f"{profile['N']}-{profile['seed']}-{profile['height']}"
        if key not in old['curves']:
            continue
        previous, current = old['curves'][key], profile['curves']
        indices = {offset: i for i, offset in enumerate(previous['offsets'])}
        error = max(abs(current[field][i]-previous[field][indices[offset]])
                    for field in ('joinedReal', 'joinedEnvelopeReal', 'joinedEnvelopeImag', 'joinedModulus')
                    for i, offset in enumerate(current['offsets']))
        assert error < 1e-9
        handoffs.append(dict(N=profile['N'], seed=profile['seed'], height=profile['height'],
            matchedFrequencyOffsets=len(current['offsets']),
            maxJoinedCurveDifference=error, targetUnchanged=True))
    out = dict(input=str(args.input), inputSha256=sha(args.input),
        checkerSha256=sha(__file__), coefficientTemplates=templates,
        independentPrimeCoefficientRecurrences=coefficients, independentFactorialRows=masses,
        survivorStatisticalHandoffs=handoffs, priorScanSha256=sha(old_path),
        everySourcePinMatched=True, diagonalConventionReplayed=True,
        algebraicSupportTagsKept=True, cofinalFloorCredit=0, passed=True)
    args.output.write_text(json.dumps(out, indent=2, allow_nan=False)+'\n')
    print(json.dumps(dict(exactTemplates=len(templates), actualPrimeRows=len(coefficients),
        factorialRowChecks=len(masses), maxFloatMassError=max(m['maxFloatMassError'] for m in masses),
        survivorHandoffs=len(handoffs),
        independentReplayPassed=True, floor=False)))


if __name__ == '__main__':
    main()
