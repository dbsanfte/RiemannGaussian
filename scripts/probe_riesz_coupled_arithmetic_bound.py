#!/usr/bin/env python3
"""Optional arithmetic radius-credit regression on pinned actual prime sets.

The finite envelope below is ONLY an envelope at the listed fixed order.
It is not the independent, order-uniform Cauchy constant in the Lean theorem.
Controls are below native entry order and heights are not zero assertions.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def ball(v: arb) -> str:
    return v.str(95, radius=True)


def norm_sq(z: acb) -> arb:
    return z.real**2+z.imag**2


def main() -> None:
    ctx.prec = 640
    input_path = Path('data/riesz-coupled-signed-bound-probe.json')
    data = json.loads(input_path.read_text())
    rows = []
    for control in data['actual_prime_controls']:
        n = control['N']
        k = 13*n//32
        num,den = control['u']
        u = arb(num)/den
        cutoff = fmpz(den)**n//(fmpz(num)**n*(n+1))
        length = 2*arb(cutoff+2).log()
        b = (n+1)/(u*length)
        primes = [int(p) for p in control['primes']]
        assert all(fmpz(p).is_prime() for p in primes)
        logs = [arb(p).log() for p in primes]
        terms = [(u*x)*(-acb(arb(3)/2,control['height'])*x).exp() for x in logs]
        a = [sum(terms)]
        for i in range(1,n):
            terms = [v*(u*x)/i for v,x in zip(terms,logs)]
            a.append(sum(terms))
        w = [1/arb(n)+(1/arb(n-i) if k <= i < n-k else arb(0))-
             (b/arb(n+1-i) if i <= n-k else arb(0)) for i in range(n)]
        r = [(w[i]+w[n-1-i])/2 for i in range(n)]
        direct = sum(r[i]*(a[i]*a[n-1-i]).real for i in range(n))
        variation = sum(abs(v) for v in r)
        for qnum,qden in [(99,100),(100010,100011),(1001,1000)]:
            q = arb(qnum)/qden
            scaled = [a[i]/q**i for i in range(n)]
            energy = sum(abs(r[i])/2*(norm_sq(scaled[i])+norm_sq(scaled[n-1-i]))
                         for i in range(n))
            credit = arb(0)
            for i in range(n):
                sign = 1 if r[i] >= 0 else -1
                assert r[i] >= 0 or r[i] < 0
                credit += abs(r[i])/2*norm_sq(scaled[i]-sign*scaled[n-1-i].conjugate())
            # Certified finite envelope via upper endpoints; never extrapolated.
            envelope = arb(max(abs(v).upper() for v in scaled))
            common = q**(n-1)
            assert (direct-common*(energy-credit)).contains(0)
            assert energy <= envelope**2*variation
            upper = common*(envelope**2*variation-credit)
            absolute = envelope**2*common*variation
            assert direct < upper
            assert abs(direct) < absolute
            rows.append(dict(N=n,u=[num,den],height=control['height'],label=control['label'],
                primes=control['primes'],ratio=[qnum,qden],signed_energy_minus_credit=ball(direct),
                common_total_order_factor=ball(common),radius_diagonal_energy=ball(energy),
                radius_correlation_credit=ball(credit),finite_order_envelope=ball(envelope),
                coefficient_variation=ball(variation),signed_upper=ball(upper),
                two_sided_price=ball(absolute),order_uniform_envelope=False,
                complete_prime_population=False,native_entry_order_reached=False))
    result = dict(schema='riesz-coupled-arithmetic-bound-probe-v1',precision_bits=640,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        input_sha256=hashlib.sha256(input_path.read_bytes()).hexdigest(),rows=rows,
        actual_zero_ordinates=False,physical_masks_completed=False,
        numerical_floor_proof=False,global_floor_proved=False,proof_dependency=False,ordinary_ci=False,
        verdict='Actual finite-prime phases satisfy the common-order signed credit inequality. The fixed-order envelope is not a global Cauchy-radius certificate.')
    Path('data/riesz-coupled-arithmetic-bound-probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(rows=len(rows),precision_bits=640,numerical_floor_proof=False)))


if __name__ == '__main__':
    main()
