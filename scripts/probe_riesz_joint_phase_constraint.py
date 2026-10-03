#!/usr/bin/env python3
"""Optional finite audit of the prime-phase constraint in the joint floor.

Re-evaluate every original balanced toy atom and the SAME full head, then
hold all head-prime signs at one. Every main label has a free prime. Its
complete sign-cube average is exactly zero (proved in the companion Lean
leaf). A conditional-expectation walk also constructs adverse multiplicative
signs without enumerating the cube. These signs are NOT the logarithmic
phases at a fixed height. No native asymptotic saving or floor follows.
"""

import argparse
import cmath
from collections import Counter, defaultdict
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import probe_riesz_balanced_joint as base


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def encode(z):
    return dict(re=float(z.real), im=float(z.imag))


def total(values):
    values = tuple(values)
    return complex(math.fsum(z.real for z in values),
                   math.fsum(z.imag for z in values))


def prepare(N):
    data = base.prepare(N, 10001/20000)
    physical = 20000**(2*N)//10001**(2*N)
    # Use the ENTIRE candidate head support, including prime pairs whose
    # original sieve weight is zero. This matches the larger support used
    # by the Lean geometry lemma, rather than only its nonzero terms.
    owner_top = math.floor(math.exp(1.25*N))
    _, prime = base.arithmetic(owner_top)
    fixed = set()
    for p in range(math.ceil(math.exp(1.02*N)), owner_top+1):
        if not prime[p] or not N*N < p < physical:
            continue
        fixed.add(p)
        qlo = math.floor(math.exp(1.95*N-math.log(p)))
        qhi = math.floor(math.exp(2.03*N-math.log(p)))
        fixed.update(q for q in range(qlo+1, qhi+1) if prime[q])
    assert all(p in fixed and q in fixed for p, q, _, _ in data['headPairs'])
    atoms = []
    for n, ps, ds in data['labels']:
        A, B = 0, [0]*len(ps)
        for mask, (d, mu) in enumerate(ds):
            if d > physical:
                continue
            A += mu
            for i in range(len(ps)):
                if mask & (1 << i):
                    B[i] += mu
        R = A*data['L']-math.fsum(v*math.log(p) for v, p in zip(B, ps))
        T = math.log(n)
        amplitude = -R*math.exp((N+1)*math.log(data['u'])-1.5*T+
            (N+1)*math.log(T)-math.lgamma(N+1))/data['L']
        free = tuple(p for p in ps if p not in fixed)
        assert free
        assert all(p < math.exp(1.02*N) for p in ps)
        atoms.append((n, T, amplitude, free, len(ps)))
    return data, atoms, fixed


def sign_audit(data, atoms, fixed, window):
    selected = [row for row in atoms if window[0]*data['N'] < row[1]
                <= window[1]*data['N']]
    primes = sorted({p for _, _, _, free, _ in selected for p in free})
    index = {p: i for i, p in enumerate(primes)}
    raw_groups = defaultdict(list)
    for _, _, amplitude, free, _ in selected:
        mask = sum(1 << index[p] for p in free)
        assert mask
        raw_groups[mask].append(amplitude)
    groups = {mask: math.fsum(values) for mask, values in raw_groups.items()}
    assert 0 not in groups
    head = math.fsum((data['L']-math.log(p))*w
                    for p, _, w, _ in data['headPairs'])
    assert head >= 0
    by_last = defaultdict(list)
    for mask, amplitude in groups.items():
        by_last[mask.bit_length()-1].append((mask, amplitude))
    negative = 0
    joined_mean = -head
    increments = []
    for i in range(len(primes)):
        coefficient = math.fsum(amplitude*(-1 if (mask & negative).bit_count() % 2 else 1)
                                for mask, amplitude in by_last[i])
        if coefficient > 0:
            negative |= 1 << i
        joined_mean -= abs(coefficient)
        increments.append(-abs(coefficient))
    direct = math.fsum(amplitude*(-1 if (mask & negative).bit_count() % 2 else 1)
                       for mask, amplitude in groups.items())-head
    assert abs(direct-joined_mean) < 5e-13
    assert direct <= -head+5e-13
    return dict(N=data['N'], window=list(window), labels=len(selected),
        counts=dict(Counter(row[4] for row in selected)), fixedHeadPrimes=len(fixed),
        freePrimes=len(primes), nonemptyFreeSupports=len(groups),
        everySelectedLabelHasAFreePrime=True, sameFullHeadAlwaysRetained=True,
        completeMainSignCubeAverage=0,
        completeJointSignCubeAverage=-head,
        heightZeroHead=head, conditionalExpectationJoint=direct,
        conditionalExpectationIncrementsSum=math.fsum(increments),
        allChosenSignsOnHeadPrimesAreOne=True,
        fixedSupportIncludesZeroSievePrimePairs=True,
        chosenNegativeFreePrimes=[p for i, p in enumerate(primes) if (negative >> i) & 1],
        integerDivisorFaceFullFactorialAllCountsAndOriginalHeadAllocationRetained=True,
        actualFixedHeightCharacterUsedForThisSignChoice=False,
        actualFixedHeightCarrierBoundProved=False, noCofinalFloorSaving=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--orders', nargs='+', type=int, default=[6, 7, 8])
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-joint-phase-constraint/probe.json'))
    args = ap.parse_args()
    frozen_path = Path('.lake/riesz-owner-completion/probe.json')
    frozen = json.loads(frozen_path.read_text())
    for source in frozen['sources']:
        assert digest(source['path']) == source['sha256'], source['path']
    cases, regressions = [], []
    for N in args.orders:
        data, atoms, fixed = prepare(N)
        for window in ((1.95, 2.03), (1.971, 2.029)):
            case = sign_audit(data, atoms, fixed, window)
            cases.append(case)
            print(json.dumps({k: case[k] for k in
                ('N', 'window', 'labels', 'freePrimes', 'heightZeroHead',
                 'completeJointSignCubeAverage', 'conditionalExpectationJoint')}), flush=True)
            for height in (54., 65., 100.):
                main_sum = total(amplitude*cmath.exp(-1j*height*T)
                    for _, T, amplitude, _, _ in atoms
                    if window[0]*N < T <= window[1]*N)
                head_sum = total((data['L']-math.log(p))*w*cmath.exp(-1j*height*T)
                                for p, _, w, T in data['headPairs'])
                old = next(c for c in frozen['cases'] if c['N'] == N
                           and c['height'] == height and c['window'] == list(window))
                old_main, old_head, old_joint = (complex(old[name]['re'], old[name]['im'])
                    for name in ('originalBalancedMain', 'sameFullOriginalHead', 'actualJoint'))
                assert abs(main_sum-old_main) < 5e-13
                assert abs(head_sum-old_head) < 5e-13
                assert abs(main_sum-head_sum-old_joint) < 5e-13
                regressions.append(dict(N=N, height=height, window=list(window),
                    signedMain=encode(main_sum), sameFullHead=encode(head_sum),
                    actualJoint=encode(main_sum-head_sum), frozenComplexRegressionPass=True))
    sources = [Path(__file__), Path('scripts/probe_riesz_balanced_joint.py'), frozen_path,
               Path('RiemannGaussian/ZetaRieszJointPhaseConstraint.lean')]
    report = dict(schemaVersion=1, date='2026-10-03', objective='Close out the floor.',
        sources=[dict(path=str(p), sha256=digest(p)) for p in sources],
        cases=cases, actualHeightRegressions=regressions,
        frozenComplexTotalRegressions=len(regressions),
        structuralTest='Fix the entire head-prime sign support; average all other actual-prime signs jointly across every central label.',
        signChoiceIsNotOneFixedHeightLogCharacter=True,
        toyLength='-2N log(10001/20000)', nativeMovingIntegerLength=False,
        nativeDyadicSchedule=False, fullNativeDeletionMasks=False,
        noEventualNativeBudgetApplied=True, optionalOutsideBuildsCI=True,
        numericCertificate=False, newArithmeticFloorSavingProved=False,
        fixedHeightNoGoProved=False, goalStillOpen=True)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(cases=len(cases), frozenComplexRegressions=len(regressions),
                          newFloorSaving=False)), flush=True)


if __name__ == '__main__':
    main()
