#!/usr/bin/env python3
"""Optional signed full-window phase primitive diagnostic.

This is the continuous integer-density MAIN, not an arithmetic prime
carrier, a count/physical-mask transport, or a certificate. All factorial
slots and the actual fixed phase are kept. Moving L is computed from its
exact rational floor; radial endpoints in this probe are the ideal real
endpoints, not their integer floors. Lean separately pays the actual
lattice rounding and counting errors. No unspecified finite constant is
set to one to claim a finite-order floor.
"""

import argparse
import cmath
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import mpmath as mp


def native_length(N):
    cutoff = pow(20000, N) // (pow(10001, N) * (N + 1))
    return 2 * math.log(cutoff + 2)


def normalized_primitive(N, T, u, y):
    # Exact finite primitive e^{-zT} sum of every factorial slot, factored
    # at its largest degree for stable evaluation; no truncated Taylor fit.
    z = complex(0.5, y)
    term = total = complex(1)
    for k in range(N + 1, 0, -1):
        term *= k / (z * T)
        total += term
    log_amplitude = ((N + 1) * (math.log(u) + math.log(T))
                     - T / 2 - math.lgamma(N + 1))
    return math.exp(log_amplitude) * cmath.exp(-1j * y * T) * total / z


def experiment(N, y):
    u = 10001 / 20000
    L = native_length(N)
    left = normalized_primitive(N, 39 * N / 20, u, y)
    right = normalized_primitive(N, 203 * N / 100, u, y)
    integral = left - right
    density_main_per_unit_scalar = -integral / L
    # These are coefficients of the proved bound, NOT evaluations of its
    # finite Dirichlet/counting constants.
    phase_budget = (2 / 27) * (N + 1) * u * (199 / 50) * math.exp(-N / 200000)
    sampling_budget = (2 * u * (N + 1) * (2 * (N + 1) + 3 + abs(y))
                       * math.exp(-N / 4))
    counting_coefficient = (2 * u * (4 + abs(y)) * N * (N + 1)
                            * math.exp(-N / 200))
    left_exponent = math.log(2 * u) + math.log(39 / 40) - 39 / 40 + 1
    right_exponent = math.log(2 * u) + math.log(203 / 200) - 203 / 200 + 1
    assert left_exponent < 0 and right_exponent < 0
    assert abs(integral.real) <= phase_budget + sampling_budget + 1e-9
    assert math.isfinite(abs(integral))
    return dict(
        N=N, height=y, nativeMovingLength=L,
        normalizedIntegral=dict(re=integral.real, im=integral.imag),
        normalizedDensityMainPerUnitScalar=dict(
            re=density_main_per_unit_scalar.real,
            im=density_main_per_unit_scalar.imag),
        continuousMainAbsAllowanceFromDensityBound=7 * abs(integral) / L,
        endpointExponents=dict(left=left_exponent, right=right_exponent),
        provedPhaseBudget=phase_budget, provedSamplingBudget=sampling_budget,
        provedCountingErrorCoefficient=counting_coefficient,
        centralRadialErrorCoefficient=math.exp(-N / 1000000),
        noArithmeticPrimeEnumeration=True, noBoundaryPaymentInferred=True,
        noFloorOrZeroExclusionClaim=True)


def independent_primitive_regressions():
    # Independently use the incomplete-Gamma integral rather than the
    # factorial endpoint recurrence used by the main diagnostic.
    checks = []
    with mp.workdps(70):
        for N, y in ((256, 54), (640, 65), (1536, 100)):
            z = mp.mpc('0.5', y)
            u = mp.mpf(10001) / 20000
            exact = (u**(N+1) * mp.gammainc(
                N+2, z * mp.mpf(39) * N / 20, z * mp.mpf(203) * N / 100)
                / (mp.factorial(N) * z**(N+2)))
            value = (normalized_primitive(N, 39*N/20, float(u), y)
                     - normalized_primitive(N, 203*N/100, float(u), y))
            relative_error = float(abs(mp.mpc(value)-exact) / abs(exact))
            assert relative_error < 2e-9
            checks.append(dict(N=N, height=y, precisionDigits=70,
                               relativeError=relative_error))
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rows = [experiment(N, y) for N in (256, 640, 1536, 4096, 8192, 32768, 65536)
            for y in (54, 65, 100)]
    report = dict(
        schemaVersion=1, diagnosticOnly=True,
        scope='Complete continuous signed integer-density phase integral',
        fullPhaseRetained=True, allFactorialSlotsRetained=True,
        movingLengthUsesExactRationalFloor=True,
        latticeEndpointsAreIdealInProbe=True,
        leanSeparatelyPaysLiteralLatticeAndCountingError=True,
        noUnspecifiedConstantNumericallyEvaluated=True,
        noNativeMaskOrPrimeSumBoundInferred=True,
        independentPrimitiveRegressions=independent_primitive_regressions(), rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    for N in (256, 640, 1536, 4096, 8192, 32768, 65536):
        values = [r['continuousMainAbsAllowanceFromDensityBound'] for r in rows if r['N'] == N]
        print(f'N={N}: continuous signed density-main diagnostic <= {max(values):.12g}')
    print('No literal boundary or cofinal floor has been certified.')


if __name__ == '__main__':
    main()
