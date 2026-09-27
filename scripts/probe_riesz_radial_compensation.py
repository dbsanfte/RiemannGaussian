#!/usr/bin/env python3
"""Optional density diagnostic for the proved radial compensation.

The moment order remains N while M ranges over the literal radialIndices.
No primes are enumerated, no density transport is justified, and allocation
and other arithmetic eligibility masks are omitted. Quadrature is not
certified. Only Lean's actual-count argument proves the signed comparison.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.stats import qmc

from probe_riesz_quadruple_compensation import coefficient, observation
from probe_riesz_joint_core import length


def rows(N, seed, power=17, y=54.0):
    h = 1/(10*(abs(y)+1))
    L = length(N)
    mlo = 39*N//40+1
    mhi = (203*N-100)//200
    cells = mhi-mlo+1
    uv = qmc.Sobol(8, scramble=True, seed=seed).random_base2(power)
    M = mlo+np.floor(cells*uv[:, 0])
    v = ((math.pi-abs(y)*2*M) % (2*math.pi))/abs(y)
    side = np.floor(M/(125*h))
    i, j, k = (np.floor(side*uv[:, a]) for a in (1, 2, 3))
    starts = np.column_stack((.44*M+i*h, .48*M+j*h, .52*M+k*h,
                              .56*M-(i+j+k)*h+v))
    logs4 = starts+h*uv[:, 4:]
    values4, _ = observation(logs4, N, L, y)
    supply = np.mean(values4*side**3*h**4)*cells
    assert np.all(np.diff(logs4, axis=1) > 0)
    assert np.max(coefficient(logs4, L)) < 0
    assert np.max(np.cos(y*logs4.sum(axis=1))) < -.5
    assert np.all(logs4.sum(axis=1) > 1.95*N)
    assert np.all(logs4.sum(axis=1) <= 2.03*N)
    assert supply.real > 0

    points = qmc.Sobol(4, scramble=True, seed=seed+1).random_base2(power)
    MT = mlo+np.floor(cells*points[:, 0])
    result = []
    for eta in (1e-5, 2e-5, 3e-5, 1e-4):
        x1 = eta*MT*(2*points[:, 1]-1)
        x2 = eta*MT*(2*points[:, 2]-1)
        delta = 2*points[:, 3]
        x3 = delta-x1-x2
        selected = np.abs(x3) <= eta*MT
        logs3 = 2*MT[:, None]/3+np.column_stack((x1, x2, x3))
        values3, norms3 = observation(logs3, N, L, y)
        assert np.min(coefficient(logs3, L)) > 0
        # Two-unit radial length, plus unordered triple symmetry factor.
        volume = (2*eta*MT)**2*2/6
        triple = np.mean(values3*selected*volume)*cells
        absolute = np.mean(norms3*selected*volume)*cells
        result.append(dict(
            N=N, seed=seed, samples_per_family=2**power, height=y,
            eta=eta, radial_index_min=mlo, radial_index_max=mhi,
            moving_length_over_N=L/N,
            source_scaled_triple=[float(triple.real), float(triple.imag)],
            source_scaled_supply=[float(supply.real), float(supply.imag)],
            model_triple_absolute_mass=float(absolute),
            absolute_mass_over_positive_supply=float(absolute/supply.real),
            fraction_spent_on_negative_real=float(max(-triple.real, 0)/supply.real)))
    return result


def main():
    script = Path(__file__).resolve()
    dependencies = [script, script.with_name("probe_riesz_quadruple_compensation.py"),
                    script.with_name("probe_riesz_joint_core.py")]
    data = dict(
        scope="uncertified density diagnostic across the exact radial supply indices",
        rows=[row for N in (65536, 262144) for seed in (17, 29) for row in rows(N, seed)],
        source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in dependencies},
        limitations=[
            "No actual prime counts or signed prime-density transport are computed.",
            "Allocation and further arithmetic masks are omitted.",
            "Each supply label's prime-log region is ordered and its radial slab is disjoint.",
            "The actual moment remains N, not the varying radial cell index M.",
            "Sample height 54 is not asserted to be a zero ordinate.",
            "Scrambled Sobol estimates are not certified numerical enclosures.",
            "Small signed triple averages are subject to radial phase sampling error.",
            "The independent Lean proof uses much more conservative constants.",
            "The untouched share/count complement is not estimated by this probe."])
    output = script.parents[1]/"docs/riesz-radial-compensation-probe.json"
    output.write_text(json.dumps(data, indent=2)+"\n")
    for row in data["rows"]:
        print({k: row[k] for k in ("N", "seed", "eta", "absolute_mass_over_positive_supply")}, flush=True)


if __name__ == "__main__":
    main()
