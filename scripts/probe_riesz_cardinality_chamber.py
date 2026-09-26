#!/usr/bin/env python3
"""Optional signed Riesz chamber regression, not a retained prime-sum bound.

Two independent checks: exact integer DP sums all signed subsets of unequal
rational shares; deliberately selected squarefree prime products have exact
Proth primality witnesses. Logs, phases and allocation probabilities in the
prime examples are exploratory, not interval certificates or population data.
No prime-count class or phase is removed from the arithmetic target.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

from probe_riesz_label_anatomy import check_certificate, length, proth_near_log, riesz
from probe_riesz_joint_masked import rectangle_values


def subset_dp(k):
    """Coefficient of v^j t^e in prod_(i=1)^k (1-v*t^i).

    This retains all 2^k subsets, including every subset sign; it is not a
    count truncation or a recurrence for the proposed closed kernel formula.
    """
    rows = [{0: 1}]+[{} for _ in range(k)]
    for i in range(1, k+1):
        for j in range(i, 0, -1):
            for e, c in rows[j-1].items():
                rows[j][e+i] = rows[j].get(e+i, 0)-c
    for j, row in enumerate(rows):
        assert sum(row.values()) == (-1)**j*math.comb(k, j)
    return rows


def rational_regressions():
    rows = []
    for k, m, epsilon in [(12, 4, Q(1, 1000)), (48, 16, Q(1, 100000))]:
        s, d = Q(19, 40), Q(173285, 250000)-Q(21, 40)
        scale = epsilon/Q(k*(k+1), 2)
        base = (s-epsilon)/k
        x = [base+scale*i for i in range(1, k+1)]
        assert len(set(x)) == k and sum(x) == s
        assert sum(x[-m:]) < d < sum(x[:m+1])
        dp = subset_dp(k)
        observed = sum(c*max(Q(0), d-j*base-e*scale)
                       for j, row in enumerate(dp) for e, c in row.items())
        expected = (-1)**m*(math.comb(k-1, m)*d-math.comb(k-2, m-1)*s)
        assert observed == expected and observed != 0
        rows.append(dict(cofactor_count=k, active_subset_count_through=m,
            exact_subset_count=str(2**k), distinct_coordinates=k,
            cofactor_total=str(s), remainder_cutoff=str(d), excess=str(epsilon),
            minimum_share=str(min(x)), maximum_share=str(max(x)),
            subset_dynamic_program_value=str(observed), chamber_formula=str(expected),
            all_subsets_identity_error='0',
            meaning='Exact rational finite subset identity, not ordinary-prime data.'))
    return rows


def prime_example(N, k):
    lam = mp.mpf(173285)/250000
    T = length(N)/lam
    p = mp.mpf(105001)/200000  # interior, not an exact rational prime-log share
    eps = mp.mpf(1)/(1000 if k == 12 else 1000000)
    s = 1-p
    base = (s-eps)/k
    targets = [p*T]+[(base+eps*i/(k*(k+1)/2))*T for i in range(1, k+1)]
    certificates, primes = [], []
    for target in targets:
        prime, cert = proth_near_log(target)
        check_certificate(prime, cert)
        primes.append(prime)
        certificates.append(dict(prime=str(prime), **cert))
    assert len(set(primes)) == k+1
    logs = list(map(mp.log, primes))
    P, cofactors = logs[0], sorted(logs[1:])
    T, L = mp.fsum(logs), length(N)
    s, d = mp.fsum(cofactors), L-P
    m = 4 if k == 12 else 16
    # Extremal subset sums verify every chamber inequality without sampling.
    low_margin = d-mp.fsum(cofactors[-m:])
    high_margin = mp.fsum(cofactors[:m+1])-d
    assert low_margin > 0 and high_margin > 0
    H = (-1)**m*(math.comb(k-1, m)*d-math.comb(k-2, m-1)*s)
    direct_error = None
    if k == 12:
        direct_error = abs(riesz(cofactors, d)-H)
        assert direct_error < mp.mpf('1e-80')
    shares = [v/T for v in logs]
    checked = dict(squarefree=len(set(primes)) == k+1,
        count_in_3_to_55=3 <= k+1 <= 55,
        core=mp.mpf(39)*N/20 < T <= mp.mpf(203)*N/100,
        original_physical_lower=all(p > N*N for p in primes),
        original_physical_upper=all(v < L for v in logs),
        owner_interior=mp.mpf(1)/2 < shares[0] < mp.mpf(3)/5,
        least_interior=mp.mpf(1)/200 < min(shares) < mp.mpf(3)/50,
        nondominant=max(shares) < mp.mpf(13)/20,
        saturation=s < L)
    assert all(checked.values()), checked
    if k == 12:
        assert mp.mpf(693)/1000 <= L/T <= mp.mpf(347)/500
        assert min(cofactors)/T >= mp.mpf(79)/2000
        assert H/T <= -mp.mpf(123)/100
    else:
        assert mp.mpf(6931)/10000 <= L/T <= mp.mpf(1733)/2500
        assert min(cofactors)/T >= mp.mpf(1979)/200000
        assert mp.mpf(21)/40 <= P/T <= mp.mpf(52501)/100000
        assert H/T >= mp.mpf(3)/500*math.comb(47, 16)
    weight = rectangle_values(N, np.array([float(P/T)]), np.array([float(min(cofactors)/T)]))[0]
    coefficient = T*H/L
    phase = mp.exp(-1j*60*T)
    return dict(N=N, prime_count=k+1, certificates=certificates,
        total_log=mp.nstr(T, 40), moving_length=mp.nstr(L, 40),
        cutoff_ratio=mp.nstr(L/T, 40), owner_share=mp.nstr(P/T, 40),
        least_share=mp.nstr(min(cofactors)/T, 40),
        active_subset_count_through=m,
        all_active_margin_per_log_n=mp.nstr(low_margin/T, 30),
        all_inactive_margin_per_log_n=mp.nstr(high_margin/T, 30),
        reduced_riesz_per_log_n=mp.nstr(H/T, 40),
        coefficient_per_log_n=mp.nstr(coefficient/T, 40),
        original_rectangle_weight=float(weight),
        fixed_phase_height=60, real_phased_coefficient_per_log_n=mp.nstr((coefficient*phase).real/T, 40),
        checks=checked, direct_subset_error=None if direct_error is None else mp.nstr(direct_error, 5),
        scope='Chosen certified primes; logs/weights/phases are exploratory. '
              'No density claim, eventual bound, complete support embedding or zero hypothesis.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=2048)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.order < 2048:
        parser.error('N>=2048 is needed for the chosen distinct-prime regression.')
    mp.mp.dps = 110
    names = [Path(__file__).name, 'probe_riesz_label_anatomy.py', 'probe_riesz_joint_masked.py']
    frozen = {n: hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest() for n in names}
    report = dict(scope='Exact subset DP and deliberately chosen prime regressions, not the signed carrier bound.',
        arithmetic_target_unchanged='lowerThresholdPacket(3..55)-shortOverflowPacket(3..13)',
        rational_subset_checks=rational_regressions(), source_sha256=frozen, prime_examples=[])
    for k in [12, 48]:
        row = prime_example(args.order, k)
        report['prime_examples'].append(row)
        print(json.dumps({key: value for key, value in row.items() if key != 'certificates'}), flush=True)
    assert frozen == {n: hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest() for n in names}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
