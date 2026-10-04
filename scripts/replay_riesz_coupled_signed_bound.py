#!/usr/bin/env python3
"""Independent 420-bit replay of the joined signed bound; no producer import."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def norm_sq(v: acb) -> arb:
    return v.real**2+v.imag**2


def main() -> None:
    ctx.prec = 420
    source_path = Path('data/riesz-coupled-signed-bound-probe.json')
    data = json.loads(source_path.read_text())
    checks = 0
    widths = 0

    def check(value: arb, stored: str) -> None:
        nonlocal checks,widths
        enclosure = arb(stored)
        assert enclosure.contains(value),(stored,str(value))
        checks += 1
        if not enclosure.contains(0):
            assert enclosure.rad()/abs(enclosure.mid()) < arb('1e-85')
            widths += 1

    def check_complex(value: acb, stored: list[str]) -> None:
        check(value.real,stored[0])
        check(value.imag,stored[1])

    for row in data['coefficient_rows']:
        n,k = row['N'],row['K']
        num,den = row['u']
        u = arb(num)/den
        d = fmpz(den)**n//(fmpz(num)**n*(n+1))
        length = 2*arb(d+2).log()
        b = arb(n+1)/(u*length)
        variation, signed = arb(0), arb(0)
        for i in range(n//2):
            if i < k-1:
                r = 1/arb(n)-b/(2*arb(n+1-i))
            elif i == k-1:
                r = 1/arb(n)-b/2*(1/arb(n+1-i)+1/arb(i+2))
            else:
                r = (1/arb(n)+(1/arb(n-i)+1/arb(i+1))/2-
                     b/2*(1/arb(n+1-i)+1/arb(i+2)))
            variation += 2*abs(r)
            signed += 2*r
        central = sum(1/arb(j) for j in range(k+1,n-k+1))
        prefix = sum(1/arb(j) for j in range(k+1,n+2))
        assert (signed-(1+central-b*prefix)).contains(0)
        separate = 1+central+b*prefix
        credit = variation-signed
        limit = 1+(arb(19)/13).log()+(arb(32)/13).log()/(2*u*u.log())
        for field,value in [
            ('length',length),('length_factor',b),
            ('separate_coefficient_price',separate),('joined_coefficient_price',variation),
            ('constant_array_credit',credit),('constant_array_value',signed),
            ('remaining_target_gap',signed-arb(399)/5000),
            ('constant_array_source_limit',limit),('limiting_target_gap',limit-arb(399)/5000)]:
            check(value,row[field])

    for row in data['actual_prime_controls']:
        ctx.prec = 640
        n,k = row['N'],13*row['N']//32
        num,den = row['u']
        u = arb(num)/den
        d = fmpz(den)**n//(fmpz(num)**n*(n+1))
        b = arb(n+1)/(u*2*arb(d+2).log())
        primes = [int(p) for p in row['primes']]
        assert all(fmpz(p).is_prime() for p in primes)
        logs = [arb(p).log() for p in primes]
        phases = [(-acb(arb(3)/2,row['height'])*x).exp() for x in logs]
        a = [sum(z*(u*x)**(j+1)/arb(fmpz.fac_ui(j))
                 for x,z in zip(logs,phases)) for j in range(n+1)]
        original = (sum(a[i]*a[n-1-i] for i in range(n))/n+
            sum(a[i]*a[n-1-i]/(n-i) for i in range(k,n-k))-
            b*sum(a[i]*a[n-i]/(n+1-i) for i in range(n-k+1)))
        # Collect positive and negative antidiagonals separately, then reflect.
        weights = [1/arb(n) for _ in range(n)]
        for i in range(k,n-k):
            weights[i] += 1/arb(n-i)
        v = [arb(0) for _ in range(n)]
        for i in range(n-k+1):
            v[i] = 1/arb(n+1-i)
            weights[i] -= b*v[i]
        energy,credit,price = arb(0),arb(0),arb(0)
        advance = acb(0)
        for i in range(n):
            j = n-1-i
            r = (weights[i]+weights[j])/2
            sign = 1 if r >= 0 else -1
            assert r >= 0 or r < 0
            energy += abs(r)/2*(norm_sq(a[i])+norm_sq(a[j]))
            credit += abs(r)/2*norm_sq(a[i]-sign*a[j].conjugate())
            advance += b*v[i]*a[i]*(a[j]-a[j+1])
            price += abs(b)*v[i]*abs(a[i])*abs(a[j]-a[j+1])
        check_complex(original,row['full_complex_value'])
        check_complex(advance,row['signed_advance'])
        check(energy,row['diagonal_energy'])
        check(credit,row['correlation_credit'])
        check(price,row['advance_price'])
        check(energy-credit+price,row['signed_upper'])
        assert (original.real-(energy-credit+advance.real)).contains(0)
        assert original.real < energy-credit+price
    result = dict(schema='riesz-coupled-signed-bound-replay-v1',precision_bits=420,
        actual_prime_control_precision_bits=640,
        input_sha256=hashlib.sha256(source_path.read_bytes()).hexdigest(),
        replay_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        independent_from_producer=True,piecewise_reflection_replayed=True,
        direct_prime_powers_and_factorials=True,ball_comparisons=checks,
        relative_width_checks=widths,coefficient_rows=len(data['coefficient_rows']),
        actual_prime_controls=len(data['actual_prime_controls']),
        native_prime_population_bound=False,independent_floor_proved=False,passed=True)
    Path('data/riesz-coupled-signed-bound-replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
