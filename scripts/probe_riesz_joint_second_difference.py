#!/usr/bin/env python3
"""Optional same-mask signed Peano/binomial bookkeeping experiment.

All factorial components and both prefixes are joined before decomposition.
The finite prime controls are below the native proof regime; the output is
neither a prime-population bound nor a zero sample nor an ordinary CI input.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def ball(value: arb) -> str:
    return value.str(95, radius=True)


def cball(value: acb) -> list[str]:
    return [ball(value.real), ball(value.imag)]


def masses(m: int, a: arb) -> list[arb]:
    out = [(1-a)**m]
    for i in range(m):
        out.append(out[-1]*(m-i)/(i+1)*a/(1-a))
    assert (sum(out)-1).contains(0)
    return out


def weights(n: int, k: int, length: arb, m: int) -> list[arb]:
    if m == n+1:
        return [arb(2*i*(m-i))/n+arb(m if k < min(i, m-i) else 0)
                for i in range(m+1)]
    return [-arb(n+1)/length*arb(m if k < min(i, m-i) else min(i, m-i))
            for i in range(m+1)]


def expectation(b: list[arb], f: list[arb]) -> arb:
    return sum(x*y for x, y in zip(b, f))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path,
        default=Path('data/riesz-joint-second-difference-probe.json'))
    args = parser.parse_args()
    ctx.prec = 360
    seed_path = Path('data/riesz-saddle-centers-prime-seeds.json')
    seeds = json.loads(seed_path.read_text())
    rows = []
    for seed in seeds['rows']:
        n, p, q = seed['N'], int(seed['p']), int(seed['q'])
        assert fmpz(p).is_prime() and fmpz(q).is_prime()
        p, q = max(p, q), min(p, q)
        x, z = arb(p).log(), arb(q).log()
        total, a = x+z, x/(x+z)
        u, eta = arb(10001)/20000, arb(3)/100
        cutoff = fmpz(20000)**n//(fmpz(10001)**n*(n+1))
        length, k = 2*arb(cutoff+2).log(), 13*n//32
        for matching in ['selected', 'physical']:
            delta = eta/arb(n+1).sqrt()
            theta = (delta/u).atan() if matching == 'selected' else 2*delta
            slope = theta/delta
            original, comparison = arb(0), arb(0)
            symbol_rows = []
            for m in [n+1, n+2]:
                b0, b1, b2 = (masses(m-j, a) for j in range(3))
                c = weights(n, k, length, m)
                freq = [slope*(2*i-m)-(x-z) for i in range(m+1)]
                factorial_scale = total**m/arb(fmpz.fac_ui(m))
                original += factorial_scale*expectation(b0, c)
                comparison += factorial_scale*expectation(b0,
                    [c[i]*(delta*freq[i]).cos() for i in range(m+1)])
                jumps = sorted({k-1,k,m-k-2,m-k-1})
                dc = [c[i+1]-c[i] for i in range(m)]
                ddc = [c[i+2]-2*c[i+1]+c[i] for i in range(m-1)]
                constant = -arb(4)/n if m == n+1 else arb(0)
                for i in range(m-1):
                    if i not in jumps:
                        assert (ddc[i]-constant).contains(0)
                for t_num, t_den in [(0,1), (1,2), (1,1)]:
                    t = arb(t_num)/t_den
                    g = [(t*delta*f).cos() for f in freq]
                    f = [c[i]*g[i] for i in range(m+1)]
                    df = [f[i+1]-f[i] for i in range(m)]
                    dg = [g[i+1]-g[i] for i in range(m)]
                    ddg = [g[i+2]-2*g[i+1]+g[i] for i in range(m-1)]
                    detuning = slope*(2*m*a-m)-(x-z)
                    v = arb(m)*a*(1-a)
                    w = arb(m*(m-1))*a*a*(1-a)**2
                    parts = dict(
                        detuning=detuning**2*expectation(b0,f),
                        first_difference=4*slope*detuning*v*expectation(b1,df),
                        variance=4*slope*slope*v*expectation(b1,
                            [a*f[i]+(1-a)*f[i+1] for i in range(m)]),
                        polynomial_curvature=4*slope*slope*w*expectation(b2,
                            [constant*g[i+1] for i in range(m-1)]),
                        mask_jumps=4*slope*slope*w*expectation(b2,
                            [(ddc[i]-constant)*g[i+1] if i in jumps else arb(0)
                             for i in range(m-1)]),
                        phase_curvature=4*slope*slope*w*expectation(b2,
                            [c[i+1]*ddg[i] for i in range(m-1)]),
                        cross_jumps=4*slope*slope*w*expectation(b2,
                            [dc[i+1]*dg[i+1]+dc[i]*dg[i] for i in range(m-1)]))
                    direct = expectation(b0,[freq[i]**2*f[i] for i in range(m+1)])
                    assert (direct-sum(parts.values())).contains(0)
                    scale = factorial_scale*delta**2
                    symbol_rows.append(dict(degree=m, t=[t_num,t_den],
                        exact_jump_orders=jumps, direct=ball(scale*direct),
                        joined_parts={name:ball(scale*value) for name,value in parts.items()}))
            curvature = original-comparison
            for height in [55,142]:
                phase = (-acb(arb(3)/2,height)*total).exp()*u**(n+1)/(n+1)
                output_symbols=[]
                for row in symbol_rows:
                    output_symbols.append(dict(**row,
                        signed_direct=cball(phase*arb(row['direct'])),
                        signed_parts={name:cball(phase*arb(value))
                            for name,value in row['joined_parts'].items()}))
                rows.append(dict(N=n,p=str(p),q=str(q),height=height,
                    source_box=seed['box'],matching=matching,K=k,
                    theta=ball(theta),delta=ball(delta),length=ball(length),
                    original=cball(phase*original),comparison=cball(phase*comparison),
                    signed_curvature=cball(phase*curvature),
                    joint=cball(phase*(comparison+curvature)),symbols=output_symbols))
    result=dict(schema='riesz-joint-second-difference-v1',precision_bits=360,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        input_sha256=hashlib.sha256(seed_path.read_bytes()).hexdigest(),
        actual_prime_controls=True,actual_zeros=False,native_core_membership=False,
        native_prime_population_bound=False,proof_dependency=False,ordinary_ci=False,
        independent_floor_proved=False,row_count=len(rows),rows=rows,
        verdict='Joint multiplier is one. Order-mask curvature has only five possible joined boundaries; variance, phase curvature and cross jumps remain signed and coupled.')
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(rows=len(rows),symbols=sum(len(r['symbols']) for r in rows),
        original_equals_joint=True,independent_floor_proved=False),indent=2))


if __name__ == '__main__':
    main()
