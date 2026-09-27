#!/usr/bin/env python3
"""Optional quantitative diagnostic for ZetaRieszBandCompensation.

No actual primes are enumerated. The density model retains the new 3-D
supply grid, whole triple-band geometry, exact subset coefficient, moving
length, factorial weight and phase. Allocation and further arithmetic
masks are omitted. Neither quadrature nor finite starting orders are
certified. The Lean proof does not depend on this script.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import qmc

from probe_riesz_quadruple_compensation import coefficient, observation
from probe_riesz_joint_core import length


def proof_witness(y):
    """Floating evaluation of the explicit constants chosen in the proofs.

    These are not enclosures. The eventual PNT threshold is not evaluated.
    """
    h = 1/(10*(abs(y)+1))
    C = 2*math.pi/abs(y)
    interval_c = math.expm1(h)/(2*(1+h))
    supply_c = interval_c**4/(500*h)**3/80*math.exp(-1.5*(C+4*h))
    triple_B = 27*(6*math.log(4))**3*math.exp(5.5)
    eta = min(.001, math.sqrt(supply_c/(2*triple_B)))
    return dict(height=y, h=h, C=C, interval_constant=interval_c,
                supply_constant=supply_c, triple_constant=triple_B,
                eta_witness_approx=eta,
                note="floating diagnostic, no certified eta or effective starting order")


def rows(N, seed, power=16, y=54.0):
    h = 1/(10*(abs(y)+1))
    v = ((math.pi-abs(y)*2*N) % (2*math.pi))/abs(y)
    L = length(N)
    M = math.floor(N/(125*h))
    uv = qmc.Sobol(7, scramble=True, seed=seed).random_base2(power)
    i, j, k = (np.floor(M*uv[:, a]) for a in range(3))
    starts = np.column_stack((.44*N+i*h, .48*N+j*h,
                              .52*N+k*h, .56*N-(i+j+k)*h+v))
    logs4 = starts+h*uv[:, 3:]
    values4, _ = observation(logs4, N, L, y)
    Y = np.mean(values4)*(M**3*h**4)
    assert np.all(np.diff(logs4, axis=1) > 0)
    assert np.max(coefficient(logs4, L)) < 0
    assert np.max(np.cos(y*logs4.sum(axis=1))) < -.5
    assert Y.real > 0

    uv3 = qmc.Sobol(3, scramble=True, seed=seed+1).random_base2(power)
    result = []
    for eta in (1e-5, 3e-5, 1e-4, 1e-3):
        x1, x2 = eta*N*(2*uv3[:, :2]-1).T
        delta = uv3[:, 2]
        x3 = delta-x1-x2
        selected = np.abs(x3) <= eta*N
        logs3 = 2*N/3+np.column_stack((x1, x2, x3))
        values3, norms3 = observation(logs3, N, L, y)
        assert np.min(coefficient(logs3, L)) > 0
        # All six prime orderings describe the same unordered label.
        volume = (2*eta*N)**2/6
        X = np.mean(values3*selected)*volume
        absX = np.mean(norms3*selected)*volume
        result.append(dict(
            N=N, seed=seed, samples_per_family=2**power, height=y,
            eta=eta, moving_length_over_N=L/N, phase_translation=v,
            source_scaled_triple=[float(X.real), float(X.imag)],
            source_scaled_supply=[float(Y.real), float(Y.imag)],
            model_triple_absolute_mass=float(absX),
            absolute_mass_over_positive_supply=float(absX/Y.real),
            fraction_spent_on_negative_real=float(max(-X.real, 0)/Y.real),
            half_supply_pays_model_mass=bool(absX <= Y.real/2)))
    return result


def main():
    script = Path(__file__).resolve()
    dependencies = [script, script.with_name("probe_riesz_quadruple_compensation.py"),
                    script.with_name("probe_riesz_joint_core.py")]
    data = dict(
        scope="uncertified ordinary-prime-density diagnostic, not a signed prime-sum bound",
        proof_constant_diagnostics=[proof_witness(y) for y in (54., 1000., 1e6)],
        rows=[r for N in (65536, 262144) for seed in (17, 29) for r in rows(N, seed)],
        source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies},
        limitations=[
            "Prime measures are replaced by densities without a transport theorem.",
            "Allocation and further arithmetic eligibility tests are omitted.",
            "Only the total-log interval [2N,2N+1] of the triple band is covered.",
            "The supply translation changes the phase but retains the factorial radial weight.",
            "Height 54 is a sample height, not an asserted zero ordinate.",
            "Sobol estimates have no certified integration error.",
            "Floating proof constants do not give an evaluated Lean starting index.",
            "Neither component is asserted small after source normalization.",
            "The rest of the core, including its unused positive credit, stays open."])
    output = script.parents[1]/"docs/riesz-band-compensation-probe.json"
    output.write_text(json.dumps(data, indent=2)+"\n")
    for witness in data["proof_constant_diagnostics"]:
        print(witness, flush=True)
    for entry in data["rows"]:
        print({k: entry[k] for k in ("N", "seed", "eta", "absolute_mass_over_positive_supply",
                                    "fraction_spent_on_negative_real")}, flush=True)


if __name__ == "__main__":
    main()
