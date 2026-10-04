#!/usr/bin/env python3
"""Independent coefficient, binomial, prime-phase and square-ledger replay.

Imports no producer. Closed coefficient tables check every order in every
reported rational case, including swapped incidences and the diagonal.
Small finite prime universes and synthetic mode rows receive no floor credit.
"""

import argparse
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import itertools
import json
import math
from pathlib import Path

import mpmath as mp


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def lower(M, K, q):
    mass, total = (1-q)**M, mp.mpf(0)
    for k in range(K+1):
        total += mass
        mass *= (M-k)*q/((k+1)*(1-q))
    return total


def decode(row):
    return mp.mpc(row['re'], row['im'])


def coefficient_tables(data):
    cases = 0
    for row in data['exactAlgebra']['checks']:
        N, M, K = row['N'], row['N']+1, 13*row['N']//32
        diagonal = row['repeatedPrimeDiagonal']
        assert 2*K < M
        # Direct coefficients of the four ORIGINAL components, before
        # the claimed cancellation or closed central-band decomposition.
        for total in (M, M+1):
            for i in range(total+1):
                j = total-i
                symmetry = F(1, 2) if diagonal and i == j else F(1)
                if total == M:
                    raw_c = symmetry*(M-M*int(i<=K)-M*int(j<=K)+F(2*i*j, N))
                    central_c = symmetry*((M if K<min(i, j) else 0)+F(2*i*j, N))
                    assert raw_c == central_c
                    if min(i, j) == 0:
                        assert raw_c == 0
                else:
                    raw_c = symmetry*(-M*(M+1)+M*(i*int(j<=K)+j*int(i<=K)))
                    central_c = -symmetry*M*(M+1) if K<min(i, j) else -F(M*min(i, j))
                    assert raw_c == central_c
                    if min(i, j) == 0:
                        assert raw_c == 0
        cases += 1
    for template in data['exactAlgebra']['templates']:
        N, M, K = template['N'], template['N']+1, 13*template['N']//32
        diagonal = template['repeatedPrimeDiagonal']
        groups = defaultdict(lambda: [F(0), F(0)])
        for row in template['raw']:
            assert row['support'] == 'complete-symmetric-finite-pairs'
            assert row['phaseIdentity'] == 'prime(p)^(-s)*prime(q)^(-s)'
            key = tuple(sorted(zip(row['incidence'], row['factorialOrders'])))
            groups[key][0] += F(row['constant'])
            groups[key][1] += F(row['inverseL'])
        for key, (c, inv) in groups.items():
            (_, i), (_, j) = key
            symmetry = F(1, 2) if diagonal and i == j else F(1)
            if i+j == M:
                assert c == symmetry*((M if K<min(i, j) else 0)+F(2*i*j, N))
                assert inv == 0
            else:
                assert i+j == M+1 and c == 0
                assert inv == (-symmetry*M*(M+1) if K<min(i, j) else -F(M*min(i, j)))
    return cases


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--input', type=Path, default=Path('.lake/riesz-pair-joint-quadratic/probe.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-joint-quadratic/validation.json'))
    args = ap.parse_args()
    data = json.loads(args.input.read_text())
    for pin in data['sources']:
        assert digest(pin['path']) == pin['sha256']
    exact = coefficient_tables(data)
    errors = []
    mp.mp.dps = 110
    for row in data['finitePrimeRegressions']:
        N, M, K, u, y = row['N'], row['N']+1, 13*row['N']//32, mp.mpf(row['u']), row['y']
        L = mp.mpf(7)*M/5
        primes = row['finitePrimeUniverse']
        assert all(p>1 and all(p%d for d in range(2, math.isqrt(p)+1)) for p in primes)
        logs = {p: mp.log(p) for p in primes}
        phases = {p: mp.cos(y*logs[p])-1j*mp.sin(y*logs[p]) for p in primes}
        kernels = {p: [mp.exp(-mp.mpf(3)/2*logs[p])*phases[p]] for p in primes}
        for p in primes:
            for k in range(1, N+3):
                kernels[p].append(kernels[p][-1]*logs[p]/k)
        moments = [sum(kernels[p][k] for p in primes) for k in range(N+3)]
        parts = dict(central=mp.mpf(M)/2*sum(moments[k]*moments[M-k]
                         for k in range(K+1, M-K)),
            successor=-mp.mpf(M)*(M+1)/(2*L)*sum(moments[k]*moments[M+1-k]
                         for k in range(K+1, M+1-K)),
            logged=-mp.mpf(M)/L*sum(k*moments[k]*moments[M+1-k] for k in range(1, K+1)),
            selbergTrace=sum(mp.mpf((k+1)*(N-k))*moments[k+1]*moments[N-k]
                         for k in range(N))/N)
        direct = 0j
        for p, q in itertools.combinations(primes, 2):
            x, z, T = logs[p], logs[q], logs[p*q] if p*q in logs else mp.log(p*q)
            coefficient = T*(1-T/L)
            coefficient -= T/L*((L-x)*lower(M, K, z/T)+(L-z)*lower(M, K, x/T))
            coefficient += 2*x*z/T
            direct += coefficient*T**N/mp.factorial(N)*mp.exp(-mp.mpf(3)/2*T)*phases[p]*phases[q]
        f = lower(M, K, mp.mpf(1)/2)
        sq = []
        for order in (N, N+1):
            sq.append(sum(logs[p]*(2*logs[p])**order/mp.factorial(order)*
                          mp.exp(-3*logs[p])*phases[p]**2 for p in primes))
        diagonal = (2*f-mp.mpf(3)/2)*sq[0]+M/L*(1-f)*sq[1]
        quadratic = sum(parts.values())
        assert abs(u**M*(direct-quadratic-diagonal)) < mp.mpf('1e-85')
        for name, value in (('sourceScaledDirect', direct), ('sourceScaledQuadratic', quadratic),
                            ('sourceScaledJoinedSquare', diagonal)):
            error = abs(decode(row[name])-u**M*value)
            assert error < mp.mpf('1e-80')
            errors.append(error)
        for name, value in parts.items():
            assert abs(decode(row['sourceScaledParts'][name])-u**M*value) < mp.mpf('1e-80')
        square_budget = mp.mpf(17)/6*u*(4*u/3)**N*sum(logs[p]/mp.mpf(p)**(mp.mpf(3)/2) for p in primes)
        assert abs(square_budget-mp.mpf(row['finiteSquareBudget'])) < mp.mpf('1e-79')
        assert abs(u**M*diagonal) <= square_budget
    model_errors = []
    for row in data['pureSelectedModeNullTest']:
        N, M, K, u, L = row['N'], row['N']+1, 13*row['N']//32, mp.mpf(row['u']), mp.mpf(row['length'])
        radius = F(row['u'])
        divisor = (N+1)*radius.numerator**N
        D, remainder = divmod(radius.denominator**N, divisor)
        assert 0 <= remainder < divisor
        assert abs(L-2*mp.log(D+2)) < mp.mpf('1e-70')
        # Independent direct reciprocal sums, without harmonic/digamma.
        central = math.fsum(1/k for k in range(K+1, M-K))
        negative = math.fsum(1/k for k in range(K+1, M+1))
        value = 1+mp.mpf(central)-M/(L*u)*mp.mpf(negative)
        error = abs(value-mp.mpf(row['hypotheticalPureSelectedValue']))
        assert error < mp.mpf('1e-12')
        model_errors.append(error)
        limit = mp.mpf(row['sourceLimit'])
        source = 1+mp.log(mp.mpf(19)/13)-mp.log(mp.mpf(32)/13)/(-2*u*mp.log(u))
        assert abs(limit-source) < mp.mpf('1e-79')
        assert limit > mp.mpf(399)/5000
        assert not row['literalPrimePopulation'] and not row['independentArithmeticBound']
        assert row['cofinalFloorCredit'] == 0
    assert not data['independentSignedMainBoundProved'] and data['floorCredit'] == 0
    result = dict(inputSha256=digest(args.input), checkerSha256=digest(__file__),
        sourcePinsPassed=True, closedCoefficientCases=exact,
        finitePrimeCases=len(data['finitePrimeRegressions']),
        independentFullPhaseRecurrenceReplay=True, diagonalSpentOnce=True,
        maxPrimeReplayError=float(max(errors)), syntheticModeCases=len(model_errors),
        syntheticModeDirectSumError=float(max(model_errors)),
        optionalOutsideCI=True, independentSignedMainBoundProved=False, floorCredit=0, passed=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
