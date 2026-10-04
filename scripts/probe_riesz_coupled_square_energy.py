#!/usr/bin/env python3
"""Optional finite actual-prime square-budget regression, outside ordinary CI.

The retained native energy and credit are compared jointly. Neither a finite
prime universe nor its finite coefficient budget certifies the complete-prime
budget in Lean. The native-order rows are fixed finite head controls only.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def norm_sq(z: acb) -> arb:
    return z.real**2+z.imag**2


def main() -> None:
    ctx.prec = 640
    source = Path('data/riesz-coupled-signed-bound-probe.json')
    seeds = json.loads(source.read_text())['actual_prime_controls']
    controls = [(row, row['N']) for row in seeds]
    controls += [(seeds[0], n) for n in [4096, 65536]]
    rows = []
    for control, n in controls:
        num, den = control['u']
        u = arb(num)/den
        length = 2*arb(fmpz(den)**n//(fmpz(num)**n*(n+1))+2).log()
        b = (n+1)/(u*length)
        assert 0 < b < arb(3)/2
        primes = [int(p) for p in control['primes']]
        assert all(fmpz(p).is_prime() for p in primes)
        logs = [arb(p).log() for p in primes]
        terms = [u*x*(-acb(arb(3)/2, control['height'])*x).exp() for x in logs]
        moments = [sum(terms)]
        for i in range(1, n):
            terms = [v*u*x/i for v, x in zip(terms, logs)]
            moments.append(sum(terms))
        k = 13*n//32
        joined = [1/arb(n)+(1/arb(n-i) if k <= i < n-k else arb(0))-
                  (b/arb(n+1-i) if i <= n-k else arb(0)) for i in range(n)]
        weights = [(joined[i]+joined[n-1-i])/2 for i in range(n)]
        variation = sum(abs(w) for w in weights)
        cap = arb(4)/n
        assert all(abs(w) < cap for w in weights)
        direct = sum(weights[i]*(moments[i]*moments[n-1-i]).real for i in range(n))
        for qnum, qden in [(99, 100), (100010, 100011), (1001, 1000)]:
            q = arb(qnum)/qden
            scaled = [moments[i]/q**i for i in range(n)]
            squares = sum(norm_sq(z) for z in scaled)
            energy = sum(abs(weights[i])/2*(norm_sq(scaled[i])+norm_sq(scaled[n-1-i]))
                         for i in range(n))
            credit = arb(0)
            for i in range(n):
                sign = 1 if weights[i] >= 0 else -1
                assert weights[i] >= 0 or weights[i] < 0
                credit += abs(weights[i])/2*norm_sq(scaled[i]-sign*scaled[n-1-i].conjugate())
            common = q**(n-1)
            envelope = arb(max(abs(z).upper() for z in scaled))
            envelope_price = envelope**2*variation
            square_price = cap*squares
            assert energy < square_price
            assert energy < envelope_price
            chosen = square_price if square_price < envelope_price else envelope_price
            assert (direct-common*(energy-credit)).contains(0)
            assert direct < common*(chosen-credit)
            assert abs(direct) < common*square_price
            values = dict(signed_incidence=direct,common_order_factor=common,
                square_sum=squares,diagonal_energy=energy,correlation_credit=credit,
                coefficient_cap=cap,coefficient_variation=variation,finite_envelope=envelope,
                envelope_price=envelope_price,square_price=square_price,
                joined_signed_upper=common*(chosen-credit),two_sided_square_price=common*square_price,
                price_ratio=square_price/envelope_price)
            rows.append(dict(N=n,u=[num,den],height=control['height'],label=control['label'],
                primes=control['primes'],ratio=[qnum,qden],
                values={name: value.str(95,radius=True) for name,value in values.items()},
                square_price_chosen=bool(square_price < envelope_price),
                complete_prime_population=False,finite_order_budget_only=True,
                native_order_reached=n >= 65536))
        print(json.dumps(dict(N=n,height=control['height'],label=control['label'])), flush=True)
    result = dict(schema='riesz-coupled-square-energy-probe-v1',precision_bits=640,
        input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rows=rows,
        actual_zero_ordinates=False,numerical_floor_proof=False,global_floor_proved=False,
        proof_dependency=False,ordinary_ci=False,
        verdict='The additional signed square-budget estimate retains the negative credit. The minimum with the old price never worsens the bound. Finite controls do not bound the complete prime square budget.')
    Path('data/riesz-coupled-square-energy-probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(rows=len(rows),native_order_rows=sum(r['native_order_reached'] for r in rows))))


if __name__ == '__main__':
    main()
