#!/usr/bin/env python3
"""Optional angular diagnostic for the new literal positive-five debit.

The Lean theorem uses reciprocal prime counts, not these samples. The
continuum model is included only to compare the conservative debit to the
size of the selected box. No source-scale or phase estimate is inferred.
"""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

import numpy as np
from scipy.stats import qmc


def main():
    low, high = F(1, 10), F(9, 80)
    cutoff = (F(78068869, 113100000), F(26165377, 37700000))
    outer_mass, last_mass, coefficient = F(63, 500), F(183, 100), F(1, 6)
    envelope = outer_mass**4 * last_mass * coefficient
    assert outer_mass**4 * last_mass < F(1, 2000)
    assert envelope < F(1, 12000) < F(1, 10000)
    period_debit = 8 * F(101, 100) * F(1, 10000)
    assert period_debit < F(1, 1000) < F(1, 500)
    rows = []
    for seed in (17, 29):
        pts = qmc.Sobol(4, scramble=True, seed=seed).random_base2(18)
        shares = float(low) + float(high-low) * pts
        owner = 1 - shares.sum(axis=1)
        for lam in (float(cutoff[0]), np.log(2), float(cutoff[1])):
            d = lam-owner
            balance = np.minimum(d[:, None], shares).sum(axis=1)-3*d
            coeff = np.maximum(balance, 0)/lam
            density = coeff/(owner*np.prod(shares, axis=1))/24
            rows.append(dict(seed=seed, samples=len(pts), cutoff_ratio=float(lam),
                             model_positive_angular_mass=float(density.mean()*float(high-low)**4),
                             positive_fraction=float(np.mean(coeff > 0))))
    payload = dict(
        scope='Uncertified continuum diagnostic; the literal prime bound is proved separately in Lean.',
        cofactor_share_interval=[str(low), str(high)],
        cutoff_interval=[str(x) for x in cutoff],
        normalization='coefficient/log(n); common radial weight and phase excluded',
        rational_envelope=str(envelope), envelope_decimal=float(envelope),
        lean_local_debit='1/10000', period_envelope_per_mesh_unit=str(period_debit),
        old_period_credit='1/500', retained_period_credit='1/1000',
        rows=rows,
        limitations=['Samples do not certify prime counts, integration errors, phases or source-scale mass.',
                     'The literal theorem retains the original allocation and all masks; the model drops allocation.',
                     'The counting proof safely overcounts the four cofactor orders; the model divides by 24.',
                     'Only this fixed five-prime sector is paid. The remaining joint floor and ceiling are open.'],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out = Path(__file__).resolve().parents[1]/'docs/riesz-positive-five-payment-probe.json'
    out.write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps(payload, indent=2))


if __name__ == '__main__':
    main()
