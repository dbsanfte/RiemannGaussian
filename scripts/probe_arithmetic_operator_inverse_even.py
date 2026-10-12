#!/usr/bin/env python3
"""Diagnostic inverse-even audit. Exact rational tests are not Lean input.

All moduli/units are literal integers. Rational amplitude controls are
NOT actual prime phases. The Fourier and height tests are floating and
establish no zero source or asymptotic estimate for the projected packet.
"""

from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
import cmath
import json
import math


@dataclass(frozen=True)
class R:
    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)

    def __add__(self, other):
        return R(self.re + other.re, self.im + other.im)

    def __sub__(self, other):
        return R(self.re - other.re, self.im - other.im)

    def __mul__(self, other):
        return R(self.re * other.re - self.im * other.im,
                 self.re * other.im + self.im * other.re)

    def __truediv__(self, value):
        return R(self.re / value, self.im / value)

    def conjugate(self):
        return R(self.re, -self.im)

    def serial(self):
        return [str(self.re), str(self.im)]


def units(q):
    return [a for a in range(q) if math.gcd(a, q) == 1]


def total(values):
    return sum(values, R())


def energy(f):
    return total(v * v.conjugate() for v in f.values())


def inverse_pairing(q, f):
    return total(v * f[pow(a, -1, q)].conjugate() for a, v in f.items())


def even(q, f):
    return {a: (v + f[pow(a, -1, q)]) / 2 for a, v in f.items()}


def center(f):
    mean = total(f.values()) / len(f)
    return {a: v - mean for a, v in f.items()}


def totients(bound):
    phi = list(range(bound + 1))
    phi[1] = 1
    for p in range(2, bound + 1):
        if phi[p] == p:
            for d in range(p, bound + 1, p):
                phi[d] -= phi[d] // p
    return phi


def main():
    exact_tests = 0
    centered_tests = 0
    nontrivial_odd_profiles = 0
    examples = []
    phi = totients(8192)
    for q in range(1, 257):
        U = units(q)
        assert len(U) == phi[q]
        profiles = [
            {a: R(Fraction((a * a + 2 * a + 1) % 11 - 5, 7),
                  Fraction((3 * a + 1) % 7 - 3, 5)) for a in U},
            {a: R(Fraction(1), Fraction(0)) for a in U},
        ]
        profiles.append(center(profiles[0]))
        for index, f in enumerate(profiles):
            E, Q = energy(f), inverse_pairing(q, f)
            projected = even(q, f)
            PE, PQ = energy(projected), inverse_pairing(q, projected)
            assert Q.im == 0 and E.im == 0
            assert PE == PQ == (E + Q) / 2
            assert PE.im == 0 and PE.re >= 0
            assert even(q, projected) == projected
            odd = {a: f[a] - projected[a] for a in U}
            assert inverse_pairing(q, odd) == R() - energy(odd)
            if energy(odd).re > 0:
                nontrivial_odd_profiles += 1
            if index == 2:
                assert total(f.values()) == R()
                assert total(projected.values()) == R()
                centered_tests += 1
            exact_tests += 1
            if q in (1, 2, 5, 8, 9, 12, 25, 27, 49, 64) and index == 2:
                examples.append({"modulus": q, "unitCount": len(U),
                                 "oldInverseQuadratic": Q.serial(),
                                 "addedGram": E.serial(),
                                 "projectedPositive": PE.serial()})

    fourier_tests = []
    for q in (1, 2, 4, 5, 8, 9, 12, 25, 27, 49, 64, 81):
        U = units(q)
        alpha = {0: 0.0j}
        alpha[1 % q] = complex(1, 2)
        alpha[2 % q] = alpha.get(2 % q, 0) + complex(-1, 0.5)
        char = lambda x: cmath.exp(2j * math.pi * (x % q) / q)
        f = {a: sum(v * char(m * a) for m, v in alpha.items()) for a in U}
        old = sum(v * f[pow(a, -1, q)].conjugate() for a, v in f.items())
        gram = sum(abs(v) ** 2 for v in f.values())
        projected = {a: (v + f[pow(a, -1, q)]) / 2 for a, v in f.items()}
        joined = sum(v * projected[pow(a, -1, q)].conjugate()
                     for a, v in projected.items())
        raw_fourier = 0j
        raw_gram = 0j
        for m, am in alpha.items():
            for n, an in alpha.items():
                row = sum(char(m * a - n * pow(a, -1, q)) for a in U)
                grow = sum(char(m * a) * char(n * a).conjugate() for a in U)
                raw_fourier += am * an.conjugate() * row
                raw_gram += am * an.conjugate() * grow
        error = max(abs(raw_fourier - old), abs(raw_gram - gram),
                    abs(joined - (gram + old) / 2))
        assert error < 1e-9
        fourier_tests.append({"modulus": q, "maxLedgerError": error,
                              "projectedReal": joined.real})

    heights = []
    c = 6 / math.pi ** 2
    for y in (54, 65, 100):
        value = 0j
        snapshots = []
        for q in range(1, 8193):
            value += (phi[q] - c * q) * cmath.exp(-1j * y * math.log(q)) / 2
            if q in (512, 2048, 8192):
                snapshots.append({"cutoff": q, "norm": abs(value),
                                  "normOverCutoff": abs(value) / q})
        heights.append({"height": y, "density": c, "snapshots": snapshots})

    report = {
        "checksPassed": True,
        "proofInput": False,
        "exactModuliIncludingProperPowers": 256,
        "exactRationalProjectionLedgers": exact_tests,
        "exactCenteredProjectionTests": centered_tests,
        "nontrivialOddProfilesRemoved": nontrivial_odd_profiles,
        "rationalAmplitudesAreNotActualPrimeHeightPhases": True,
        "exactCenteredExamples": examples,
        "floatingFourierTests": fourier_tests,
        "floatingActualDenominatorHeightTests": heights,
        "actualZeroSourceOfWholeProjectedPacketEstablished": False,
        "asymptoticOrRHProofClaimed": False,
        "scope": "inverse-even projection adds full unit Gram; diagnostic all-modulus ledgers retain diagonal, density and endpoints",
    }
    target = Path('.lake/arithmetic-operator-inverse-even/probe.json')
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({"passed": True, "exactLedgers": exact_tests,
                      "centered": centered_tests,
                      "floatingFourierTests": len(fourier_tests),
                      "report": str(target)}))


if __name__ == '__main__':
    main()
