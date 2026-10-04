#!/usr/bin/env python3
"""Independent 760-bit replay; direct factorials and real trig phases."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def main() -> None:
    ctx.prec = 760
    path = Path('data/riesz-coupled-arithmetic-bound-probe.json')
    source = json.loads(path.read_text())
    checks = 0
    widths = 0

    def check(value: arb, stored: str) -> None:
        nonlocal checks,widths
        enclosure = arb(stored)
        assert enclosure.contains(value),(str(value),stored)
        checks += 1
        if not enclosure.contains(0):
            assert enclosure.rad()/abs(enclosure.mid()) < arb('1e-85')
            widths += 1

    for row in source['rows']:
        n = row['N']
        k = 13*n//32
        unum,uden = row['u']
        qnum,qden = row['ratio']
        u,q = arb(unum)/uden,arb(qnum)/qden
        physical = fmpz(uden)**n//(fmpz(unum)**n*(n+1))
        b = (n+1)/(u*2*arb(physical+2).log())
        primes = [int(p) for p in row['primes']]
        assert all(fmpz(p).is_prime() for p in primes)
        logs = [arb(p).log() for p in primes]
        modes = []
        for p,x in zip(primes,logs):
            angle = row['height']*x
            modes.append(acb(angle.cos(),-angle.sin())/arb(p)**(arb(3)/2))
        a = [sum(v*(u*x)**(i+1)/arb(fmpz.fac_ui(i))
                 for x,v in zip(logs,modes)) for i in range(n)]
        r = [arb(0) for _ in range(n)]
        for i in range(n//2):
            if i < k-1:
                weight = 1/arb(n)-b/(2*arb(n+1-i))
            elif i == k-1:
                weight = 1/arb(n)-b/2*(1/arb(n+1-i)+1/arb(i+2))
            else:
                weight = (1/arb(n)+(1/arb(n-i)+1/arb(i+1))/2-
                          b/2*(1/arb(n+1-i)+1/arb(i+2)))
            r[i]=r[n-1-i]=weight
        # Original incidence product, before any energy rewriting.
        signed = sum((1/arb(n)+(1/arb(n-i) if k <= i < n-k else 0)-
                      (b/arb(n+1-i) if i <= n-k else 0))*(a[i]*a[n-1-i]).real
                     for i in range(n))
        scaled = [v/q**i for i,v in enumerate(a)]
        energy,credit = arb(0),arb(0)
        for i,v in enumerate(scaled):
            other = scaled[n-1-i]
            sign = 1 if r[i] >= 0 else -1
            assert r[i] >= 0 or r[i] < 0
            energy += abs(r[i])/2*(v.real**2+v.imag**2+other.real**2+other.imag**2)
            difference = v-sign*other.conjugate()
            credit += abs(r[i])/2*(difference.real**2+difference.imag**2)
        envelope = arb(max(abs(v).upper() for v in scaled))
        common = q**(n-1)
        variation = sum(abs(v) for v in r)
        upper = common*(envelope**2*variation-credit)
        absolute = common*envelope**2*variation
        assert (signed-common*(energy-credit)).contains(0)
        assert signed < upper
        assert abs(signed) < absolute
        for field,value in [
            ('signed_energy_minus_credit',signed),('common_total_order_factor',common),
            ('radius_diagonal_energy',energy),('radius_correlation_credit',credit),
            ('finite_order_envelope',envelope),('coefficient_variation',variation),
            ('signed_upper',upper),('two_sided_price',absolute)]:
            check(value,row[field])
    result = dict(schema='riesz-coupled-arithmetic-bound-replay-v1',precision_bits=760,
        input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        replay_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        independent_from_producer=True,prime_primality_rechecked=True,
        direct_factorials_and_real_trigonometric_phases=True,rows=len(source['rows']),
        ball_comparisons=checks,relative_width_checks=widths,
        numerical_floor_proof=False,global_floor_proved=False,passed=True)
    Path('data/riesz-coupled-arithmetic-bound-replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
