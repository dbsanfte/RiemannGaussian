#!/usr/bin/env python3
"""Independent 420-bit replay of the joined Peano/factorial experiment.

Uses exact binomial coefficients, uncollected swapped prefix incidences
and direct squared frequencies. It does not import the producer. No native
prime population or zero ordinate is asserted by these finite controls.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path,nargs='?',
        default=Path('data/riesz-joint-second-difference-probe.json'))
    parser.add_argument('--output',type=Path,
        default=Path('data/riesz-joint-second-difference-replay.json'))
    args=parser.parse_args()
    ctx.prec=420
    report=json.loads(args.input.read_text())
    assert report['schema']=='riesz-joint-second-difference-v1'
    checks=0
    widths=0

    def check(expected: str,value: arb) -> None:
        nonlocal checks,widths
        saved=arb(expected)
        assert saved.contains(value),(expected,str(value))
        checks+=1
        if not value.contains(0):
            assert saved.rad()/abs(value)<arb('1e-85')
            widths+=1

    def check_complex(expected: list[str],value: acb) -> None:
        check(expected[0],value.real)
        check(expected[1],value.imag)

    for row in report['rows']:
        n,p,q=row['N'],int(row['p']),int(row['q'])
        assert p>q and fmpz(p).is_prime() and fmpz(q).is_prime()
        x,z=arb(p).log(),arb(q).log()
        total,a=x+z,x/(x+z)
        k=13*n//32
        assert row['K']==k
        u=arb(10001)/20000
        cutoff=fmpz(20000)**n//(fmpz(10001)**n*(n+1))
        length=2*arb(cutoff+2).log()
        delta=arb(3)/100/arb(n+1).sqrt()
        theta=(delta/u).atan() if row['matching']=='selected' else 2*delta
        slope=theta/delta
        check(row['length'],length)
        check(row['delta'],delta)
        check(row['theta'],theta)
        scale_phase=(-acb(arb(3)/2,row['height'])*total).exp()*u**(n+1)/(n+1)
        original,comparison=arb(0),arb(0)

        for m in [n+1,n+2]:
            def b(rank: int) -> list[arb]:
                return [arb(math.comb(rank,i))*a**i*(1-a)**(rank-i)
                        for i in range(rank+1)]

            def component_weight(i: int) -> arb:
                j=m-i
                left=1 if k<i and k<j else 0
                right=1 if k<j and k<i else 0
                if m==n+1:
                    return arb(n+1)/2*(left+right)+arb(2*i*j)/n
                low=i if 1<=i<=k else 0
                high=j if 1<=j<=k else 0
                return -arb((n+1)*(n+2))/(2*length)*(left+right)-arb(n+1)/length*(low+high)

            c=[component_weight(i) for i in range(m+1)]
            b0,b1,b2=b(m),b(m-1),b(m-2)
            factor=total**m/arb(math.factorial(m))
            freq=[slope*(2*i-m)-(x-z) for i in range(m+1)]
            original+=factor*sum(b0[i]*c[i] for i in range(m+1))
            comparison+=factor*sum(b0[i]*c[i]*(delta*freq[i]).cos() for i in range(m+1))
            for entry in [s for s in row['symbols'] if s['degree']==m]:
                t=arb(entry['t'][0])/entry['t'][1]
                g=[(t*delta*f).cos() for f in freq]
                f=[c[i]*g[i] for i in range(m+1)]
                direct=sum(b0[i]*freq[i]**2*f[i] for i in range(m+1))
                detuning=slope*(2*m*a-m)-(x-z)
                v,w=arb(m)*a*(1-a),arb(m*(m-1))*a**2*(1-a)**2
                constant=-arb(4)/n if m==n+1 else arb(0)
                parts={
                    'detuning':detuning**2*sum(b0[i]*f[i] for i in range(m+1)),
                    'first_difference':4*slope*detuning*v*
                        sum(b1[i]*(f[i+1]-f[i]) for i in range(m)),
                    'variance':4*slope**2*v*
                        sum(b1[i]*(a*f[i]+(1-a)*f[i+1]) for i in range(m)),
                    'polynomial_curvature':4*slope**2*w*
                        sum(b2[i]*constant*g[i+1] for i in range(m-1)),
                    'mask_jumps':4*slope**2*w*
                        sum(b2[i]*(c[i+2]-2*c[i+1]+c[i]-constant)*g[i+1]
                            for i in entry['exact_jump_orders']),
                    'phase_curvature':4*slope**2*w*
                        sum(b2[i]*c[i+1]*(g[i+2]-2*g[i+1]+g[i]) for i in range(m-1)),
                    'cross_jumps':4*slope**2*w*
                        sum(b2[i]*((c[i+2]-c[i+1])*(g[i+2]-g[i+1])+
                            (c[i+1]-c[i])*(g[i+1]-g[i])) for i in range(m-1))}
                assert (direct-sum(parts.values())).contains(0)
                scale=factor*delta**2
                check(entry['direct'],scale*direct)
                check_complex(entry['signed_direct'],scale_phase*scale*direct)
                for name,value in parts.items():
                    check(entry['joined_parts'][name],scale*value)
                    check_complex(entry['signed_parts'][name],scale_phase*scale*value)
        check_complex(row['original'],scale_phase*original)
        check_complex(row['comparison'],scale_phase*comparison)
        check_complex(row['signed_curvature'],scale_phase*(original-comparison))
        check_complex(row['joint'],scale_phase*original)
    result=dict(schema='riesz-joint-second-difference-replay-v1',precision_bits=420,
        independent_from_producer=True,uncollected_prefixes_replayed=True,
        input_sha256=hashlib.sha256(args.input.read_bytes()).hexdigest(),
        replay_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        ball_comparisons=checks,relative_width_checks=widths,rows=len(report['rows']),
        signed_symbols=sum(len(row['symbols']) for row in report['rows']),
        native_prime_population_bound=False,independent_floor_proved=False,passed=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
