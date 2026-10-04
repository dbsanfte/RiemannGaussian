#!/usr/bin/env python3
"""Independent higher-precision replay; does not import the producer."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def norm_sq(z: acb) -> arb:
    return z.real**2+z.imag**2


def main() -> None:
    ctx.prec = 760
    source = Path('data/riesz-coupled-square-energy-probe.json')
    data = json.loads(source.read_text())
    checks = 0
    width_checks = 0
    for row in data['rows']:
        n = row['N']
        u = arb(row['u'][0])/row['u'][1]
        q = arb(row['ratio'][0])/row['ratio'][1]
        head = fmpz(row['u'][1])**n//(fmpz(row['u'][0])**n*(n+1))
        b = (n+1)/(2*u*arb(head+2).log())
        k = 13*n//32
        primes = [int(p) for p in row['primes']]
        assert all(fmpz(p).is_prime() for p in primes)
        logs = [arb(p).log() for p in primes]
        # Rescale each literal prime atom BEFORE the recurrence, unlike the producer.
        atoms = [u*x*(-acb(arb(3)/2,row['height'])*x).exp() for x in logs]
        scaled = [sum(atoms)]
        for i in range(1,n):
            atoms = [v*(u*x/q)/i for v,x in zip(atoms,logs)]
            scaled.append(sum(atoms))
        weights = []
        for i in range(n):
            reflected = n-1-i
            positive = (1/arb(n)+(1/arb(n-i) if k <= i < n-k else 0)+
                        1/arb(n)+(1/arb(n-reflected) if k <= reflected < n-k else 0))/2
            negative = b*((1/arb(n+1-i) if i <= n-k else 0)+
                          (1/arb(n+1-reflected) if reflected <= n-k else 0))/2
            weights.append(positive-negative)
        common = q**(n-1)
        direct = common*sum(weights[i]*(scaled[i]*scaled[n-1-i]).real for i in range(n))
        squares = sum(norm_sq(z) for z in scaled)
        energy = sum(abs(weights[i])*norm_sq(scaled[i]) for i in range(n))
        credit = sum(abs(weights[i])/2*norm_sq(scaled[i]-(1 if weights[i] >= 0 else -1)*
                     scaled[n-1-i].conjugate()) for i in range(n))
        cap = arb(4)/n
        variation = sum(abs(w) for w in weights)
        envelope = arb(max(abs(z).upper() for z in scaled))
        old_price = envelope**2*variation
        price = cap*squares
        chosen = price if price < old_price else old_price
        values = dict(signed_incidence=direct,common_order_factor=common,square_sum=squares,
            diagonal_energy=energy,correlation_credit=credit,coefficient_cap=cap,
            coefficient_variation=variation,finite_envelope=envelope,
            envelope_price=old_price,square_price=price,joined_signed_upper=common*(chosen-credit),
            two_sided_square_price=common*price,price_ratio=price/old_price)
        assert row['square_price_chosen'] == bool(price < old_price)
        assert all(abs(w) < cap for w in weights)
        assert energy < price
        assert energy < old_price
        assert (direct-common*(energy-credit)).contains(0)
        assert direct < common*(chosen-credit)
        assert abs(direct) < common*price
        for name, value in values.items():
            stored = arb(row['values'][name])
            assert stored.overlaps(value), (n,row['ratio'],name)
            checks += 1
            # Every reported value is independently computed with a narrow ball.
            assert value.rel_accuracy_bits() >= 250, (n,row['ratio'],name,value)
            width_checks += 1
        print(json.dumps(dict(N=n,ratio=row['ratio'],checked=True)),flush=True)
    report = dict(schema='riesz-coupled-square-energy-replay-v1',precision_bits=760,
        input_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        replay_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        rows=len(data['rows']),ball_checks=checks,width_checks=width_checks,passed=True,
        complete_prime_population=False,numerical_floor_proof=False,proof_dependency=False,
        ordinary_ci=False)
    Path('data/riesz-coupled-square-energy-replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    main()
