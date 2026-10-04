#!/usr/bin/env python3
"""Optional ball audit of the whole joined order inequality.

Native-order rows are coefficient/constant-array audits, not prime bounds.
Finite actual-prime controls use all factorial orders at N=256, below the
native entry order, and test heights which are not asserted zero ordinates.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def ball(v: arb) -> str:
    return v.str(95, radius=True)


def cball(v: acb) -> list[str]:
    return [ball(v.real), ball(v.imag)]


def geometry(n: int, num: int, den: int):
    u = arb(num)/den
    cutoff = fmpz(den)**n//(fmpz(num)**n*(n+1))
    length = 2*arb(cutoff+2).log()
    b = (n+1)/(u*length)
    k = 13*n//32
    pos = [1/arb(n)+(1/arb(n-i) if k <= i < n-k else 0)
           for i in range(n)]
    succ = [1/arb(n+1-i) if i <= n-k else arb(0) for i in range(n)]
    joined = [pos[i]-b*succ[i] for i in range(n)]
    sym = [(joined[i]+joined[n-1-i])/2 for i in range(n)]
    return u, length, b, k, pos, succ, sym


def coefficient_row(n: int, num: int, den: int) -> dict:
    """Stream reflected rows; never store a million-order coefficient array."""
    u = arb(num)/den
    cutoff = fmpz(den)**n//(fmpz(num)**n*(n+1))
    length = 2*arb(cutoff+2).log()
    b = (n+1)/(u*length)
    k = 13*n//32
    variation, source, separate = arb(0), arb(0), arb(0)
    direct = arb(1)
    for i in range(n):
        j = n-1-i
        p = 1/arb(n)+(1/arb(n-i) if k <= i < n-k else 0)
        v = 1/arb(n+1-i) if i <= n-k else arb(0)
        pj = 1/arb(n)+(1/arb(n-j) if k <= j < n-k else 0)
        vj = 1/arb(n+1-j) if j <= n-k else arb(0)
        r = ((p-b*v)+(pj-b*vj))/2
        variation += abs(r)
        source += r
        separate += p+b*v
        if k <= i < n-k:
            direct += 1/arb(n-i)
        if i <= n-k:
            direct -= b/arb(n+1-i)
    credit = variation-source
    assert (direct-source).contains(0)
    assert (variation-credit-source).contains(0)
    if n >= 65536:
        assert variation < separate-arb(1)/3
        assert variation < arb(7)/50
    limit_b = -1/(2*u*u.log())
    source_limit = 1+(arb(19)/13).log()-limit_b*(arb(32)/13).log()
    return dict(N=n,u=[num,den],K=k,length=ball(length),length_factor=ball(b),
        separate_coefficient_price=ball(separate),joined_coefficient_price=ball(variation),
        constant_array_credit=ball(credit),constant_array_value=ball(source),
        remaining_target_gap=ball(source-arb(399)/5000),
        constant_array_source_limit=ball(source_limit),
        limiting_target_gap=ball(source_limit-arb(399)/5000),
        native_entry_order_reached=n >= 65536,actual_prime_array=False)


def norm_sq(z: acb) -> arb:
    return z.real*z.real+z.imag*z.imag


def finite_array(primes: list[int], u: arb, y: int, n: int) -> list[acb]:
    parts = []
    logs = []
    for p in primes:
        assert fmpz(p).is_prime()
        x = arb(p).log()
        logs.append(u*x)
        parts.append((-acb(arb(3)/2,y)*x).exp()*(u*x))
    out = [sum(parts)]
    for k in range(1,n+1):
        parts = [z*x/k for z,x in zip(parts,logs)]
        out.append(sum(parts))
    return out


def main() -> None:
    ctx.prec = 360
    rows = []
    for n in [256,640,4096,65536,262144,1048576]:
        for num,den in [(1,2),(10001,20000)]:
            rows.append(coefficient_row(n,num,den))
    seed_path = Path('data/riesz-saddle-centers-prime-seeds.json')
    seeds = json.loads(seed_path.read_text())
    primes = sorted({int(row[z]) for row in seeds['rows'] for z in ['p','q']})
    controls = []
    # The diagonal and credit cancel by about 33 decimal digits on these
    # controls. Raise precision instead of accepting a wider residual ball.
    ctx.prec = 512
    n = 256
    u,length,b,k,pos,succ,sym = geometry(n,10001,20000)
    for label,ps in [('whole-seed-universe',primes),('alternating-seed-universe',primes[::2])]:
        for y in [55,142]:
            a = finite_array(ps,u,y,n)
            direct = (sum(a[i]*a[n-1-i] for i in range(n))/n+
                sum(a[i]*a[n-1-i]/(n-i) for i in range(k,n-k))-
                b*sum(a[i]*a[n-i]/(n+1-i) for i in range(n-k+1)))
            energy = arb(0)
            credit = arb(0)
            advance = acb(0)
            price = arb(0)
            for i,r in enumerate(sym):
                j = n-1-i
                sign = 1 if r >= 0 else -1
                assert r >= 0 or r < 0
                energy += abs(r)/2*(norm_sq(a[i])+norm_sq(a[j]))
                credit += abs(r)/2*norm_sq(a[i]-sign*a[j].conjugate())
                difference = a[j]-a[j+1]
                advance += b*succ[i]*a[i]*difference
                price += abs(b)*succ[i]*abs(a[i])*abs(difference)
            assert (direct.real-(energy-credit+advance.real)).contains(0)
            assert direct.real < energy-credit+price
            controls.append(dict(N=n,u=[10001,20000],height=y,label=label,
                primes=[str(p) for p in ps],full_complex_value=cball(direct),
                diagonal_energy=ball(energy),correlation_credit=ball(credit),
                signed_advance=cball(advance),advance_price=ball(price),
                signed_upper=ball(energy-credit+price),native_mask_completion=False))
    result = dict(schema='riesz-coupled-signed-bound-probe-v1',precision_bits=360,
        actual_prime_control_precision_bits=512,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        seed_sha256=hashlib.sha256(seed_path.read_bytes()).hexdigest(),
        coefficient_rows=rows,actual_prime_controls=controls,
        all_factorial_orders_retained=True,all_prefixes_retained=True,
        actual_zero_ordinates=False,native_prime_population_bound=False,
        independent_floor_proved=False,proof_dependency=False,ordinary_ci=False,
        verdict='The joined signed inequality holds; coherent constant arrays still exceed 399/5000. The required extra credit is not certified.')
    Path('data/riesz-coupled-signed-bound-probe.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(coefficient_rows=len(rows),actual_prime_controls=len(controls),
        ceiling_native_row=rows[-1],floor_proved=False),indent=2))


if __name__ == '__main__':
    main()
