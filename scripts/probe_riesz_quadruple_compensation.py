#!/usr/bin/env python3
"""Optional density diagnostic for the *proved* four-prime compensation.

This is not the literal prime sum or certified quadrature. It samples the
same grid and fixed log intervals as ZetaRieszQuadrupleCompensation, replacing
each prime measure by exp(t) dt/t. It retains the moving length, all subset
signs, the factorial radial kernel and the total phase. Allocation and other
literal eligibility predicates are omitted. Lean proves its comparison from
actual counts; no numerical data enter that proof. Run outside routine CI.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
from scipy.special import gammaln
from scipy.stats import qmc

from probe_riesz_joint_core import U, length


def coefficient(logs, L):
    """Finite signed Riesz subset sum, before any norm."""
    count = logs.shape[1]
    response = np.zeros(logs.shape[0])
    for mask in range(1 << count):
        subtotal = sum((logs[:, j] for j in range(count) if mask >> j & 1),
                       np.zeros(logs.shape[0]))
        response += (-1)**mask.bit_count()*np.maximum(L-subtotal, 0)
    return -logs.sum(axis=1)/L*response


def observation(logs, N, L, y):
    total = logs.sum(axis=1)
    c = coefficient(logs, L)
    # exp(total) from the density cancels two thirds of the kernel decay.
    envelope = np.exp((N+1)*math.log(U)-total/2+N*np.log(total)-gammaln(N+1))
    value = c*envelope/np.prod(logs, axis=1)
    return value*np.exp(-1j*y*total), np.abs(value)


def row(N, seed, power=15, y=54.0):
    h = 1/(10*(abs(y)+1))
    v = ((math.pi-abs(y)*2*N) % (2*math.pi))/abs(y)
    L = length(N)
    M = math.floor(N/(1000*h))
    assert 1.37*N <= L <= 1.4*N and h+v <= N/1000

    uv = qmc.Sobol(6, scramble=True, seed=seed).random_base2(power)
    i, j = np.floor(M*uv[:, 0]), np.floor(M*uv[:, 1])
    starts = np.column_stack((.44*N+i*h, .48*N+j*h,
                              np.full(len(uv), .52*N), .56*N-(i+j)*h+v))
    logs4 = starts+h*uv[:, 2:]
    values4, _ = observation(logs4, N, L, y)
    q4 = np.mean(values4)*(M*M*h**4)
    assert np.max(coefficient(logs4, L)) < 0
    assert np.max(np.cos(y*logs4.sum(axis=1))) < -.5

    u3 = qmc.Sobol(3, scramble=True, seed=seed+1).random_base2(power)
    a = 2*N/3+v/3
    logs3 = a+h*(u3+np.arange(3))
    values3, norms3 = observation(logs3, N, L, y)
    q3, n3 = np.mean(values3)*h**3, np.mean(norms3)*h**3
    assert np.min(coefficient(logs3, L)) > 0 and q4.real > 0
    # Checks the subset enumeration against the exact chamber formulas.
    t3, t4 = logs3.sum(axis=1), logs4.sum(axis=1)
    assert np.allclose(coefficient(logs3, L), t3/L*(t3-L), rtol=1e-11)
    assert np.allclose(coefficient(logs4, L), t4/L*(2*t4-3*L), rtol=1e-11)
    spend = max(-q3.real, 0)/q4.real
    return dict(N=N, seed=seed, samples_per_family=2**power, height=y,
                moving_length_over_N=L/N, log_width=h, phase_translation=v,
                grid_side=M, grid_cells=M*M,
                source_scaled_triple=[float(q3.real), float(q3.imag)],
                source_scaled_quadruple=[float(q4.real), float(q4.imag)],
                model_triple_absolute_mass=float(n3),
                positive_supply_over_triple_mass=float(q4.real/n3),
                fraction_spent=float(spend),
                normalized_joint_real=float(q3.real+q4.real),
                unused_positive_credit=float((1-spend)*q4.real))


def main():
    rows = [row(N, seed) for N in (4096, 16384, 65536, 262144) for seed in (17, 29)]
    payload = dict(
        scope="uncertified ordinary-prime-density model of the exact grid geometry",
        rows=rows,
        limitations=[
            "No actual primes are enumerated; the density replacement is unproved.",
            "The old allocation and additional arithmetic eligibility predicates are omitted.",
            "Fixed nonzero sample height 54 is not asserted to be a zero ordinate.",
            "Scrambled Sobol integration has no rigorous enclosure here.",
            "Neither finite thresholds nor a whole-core floor follow from these samples.",
            "The Lean comparison is eventual for fixed parameters and uses actual prime counts.",
            "Spending a vanishing relative fraction is not a source-normalized error bound."],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    output = Path(__file__).resolve().parents[1]/"docs/riesz-quadruple-compensation-probe.json"
    output.write_text(json.dumps(payload, indent=2)+"\n")
    for entry in rows:
        print({key: entry[key] for key in ("N", "seed", "positive_supply_over_triple_mass",
                                           "fraction_spent", "normalized_joint_real")}, flush=True)


if __name__ == "__main__":
    main()
