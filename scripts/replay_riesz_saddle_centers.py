#!/usr/bin/env python3
"""Independent 420-bit replay of optional two-center source/prime controls.

Never imports the producer. Small finite prime controls do not certify a
native order, a complete mask, an actual zero or an arithmetic floor.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from flint import acb, arb, ctx, fmpz


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, nargs='?', default=Path('data/riesz-saddle-centers-probe.json'))
    parser.add_argument('--output', type=Path, default=Path('data/riesz-saddle-centers-replay.json'))
    args = parser.parse_args()
    ctx.prec = 420
    document = json.loads(args.input.read_text())
    assert document['schema'] == 'riesz-saddle-centers-v1'
    assert document['proof_dependency'] is False and document['ordinary_ci'] is False
    checked, width_checks = 0, 0

    def compare(row: dict, key: str, value: arb | acb) -> None:
        nonlocal checked, width_checks
        if isinstance(value, acb):
            stored = acb(arb(row[key][0]), arb(row[key][1]))
            assert stored.contains(value), (key, row.get('N'))
            if abs(value) > 0:
                assert stored.real.rad()+stored.imag.rad() < abs(value)*arb('1e-85')
                width_checks += 1
            checked += 2
        else:
            stored = arb(row[key])
            assert stored.contains(value), (key, row.get('N'))
            if abs(value) > 0:
                assert stored.rad() < abs(value)*arb('1e-85')
                width_checks += 1
            checked += 1

    eta = arb(3)/100
    for row in document['source_rows']:
        num, den = row['u']
        u = arb(num)/den
        s = 1+(arb(19)/13).log()-(arb(32)/13).log()/(-2*u*u.log())
        f = (-(arb(9)/10000)/(2*u*u)).exp()
        for key, value in [('original', s), ('vertical_attenuation', f),
                ('vertical_source', f*s), ('signed_difference_source', s-f*s),
                ('headroom', arb(399)/5000-f*s), ('real_shift_source', s/f)]:
            compare(row, key, value)
        assert s*f < arb(399)/5000 and s*(1-f) > arb(1)/7000

    for row in document['finite_rows']:
        num, den = row['u']
        u, n, k, m = arb(num)/den, row['N'], row['K'], row['multiplicity']
        assert k == 13*n//32
        K = fmpz(den)**n//(fmpz(num)**n*(n+1))
        L = 2*arb(K+2).log()
        f = arb(n+1)/(u*L)
        # Harmonic differences as exact finite sums, independently from
        # the producer's digamma evaluations. Narrow count, fast enough.
        central = sum(1/arb(j) for j in range(k+1, n-k+1))
        prefix = sum(1/arb(j) for j in range(k+1, n+2))
        r = 1/(1+(eta/u)**2/arb(n+1)).sqrt()
        old = m*m*(1+central-f*prefix)
        new = m*m*r**(n+1)*(1+central-r*f*prefix)
        for key, value in [('length', L), ('delta', eta/arb(n+1).sqrt()),
                ('radius_ratio', r), ('original', old), ('matched', new), ('signed_difference', old-new)]:
            compare(row, key, value)

    for row in document['actual_prime_atoms']:
        p, q = int(row['p']), int(row['q'])
        assert fmpz(p).is_prime() and fmpz(q).is_prime()
        n, i, j, height = row['N'], row['i'], row['j'], row['height']
        u = arb(10001)/20000
        delta = eta/arb(n+1).sqrt()
        theta = (delta/u).atan()
        x, z = arb(p).log(), arb(q).log()
        argument = theta*(i-j)-delta*(x-z)
        original = x**i*z**j/arb(fmpz.fac_ui(i)*fmpz.fac_ui(j))*(
            -acb(arb(3)/2, height)*(x+z)).exp()
        compare(row, 'theta', theta)
        compare(row, 'delta', delta)
        compare(row, 'mismatch', argument)
        compare(row, 'cosine_multiplier', argument.cos())
        compare(row, 'original', original)
        compare(row, 'shifted', argument.cos()*original)
        compare(row, 'signed_curvature', (1-argument.cos())*original)
        assert row['native_core_membership_certified'] is False

    for row in document['joined_factorial_pairs']:
        n, K, height = row['N'], row['K'], row['height']
        p, q = int(row['p']), int(row['q'])
        x, z = arb(p).log(), arb(q).log()
        u = arb(10001)/20000
        integer_cutoff = fmpz(20000)**n//(fmpz(10001)**n*(n+1))
        L = 2*arb(integer_cutoff+2).log()
        delta, angle = eta/arb(n+1).sqrt(), (eta/(u*arb(n+1).sqrt())).atan()
        # Raw components BEFORE collecting, independently from the
        # producer's min-order coefficient table. Both incidences remain.
        def raw_terms():
            M = n+1
            for k in range(M+1):
                yield k, M-k, arb(M)/2
                yield M-k, k, arb(M)/2
            for k in range(M+2):
                yield k, M+1-k, -arb(M*(M+1))/(2*L)
                yield M+1-k, k, -arb(M*(M+1))/(2*L)
            for k in range(K+1):
                yield M-k, k, -arb(M)
                yield k, M-k, -arb(M)
                yield M-k+1, k, arb(M*(M-k+1))/L
                yield k, M-k+1, arb(M*(M-k+1))/L
            for k in range(n):
                yield k+1, n-k, arb((k+1)*(n-k))/n
                yield n-k, k+1, arb((k+1)*(n-k))/n
        old, difference = arb(0), arb(0)
        for i, j, coefficient in raw_terms():
            value = coefficient*x**i*z**j/arb(fmpz.fac_ui(i)*fmpz.fac_ui(j))
            old += value
            difference += value*(1-(angle*(i-j)-delta*(x-z)).cos())
        phase = (-acb(arb(3)/2, height)*(x+z)).exp()*u**(n+1)/arb(n+1)
        compare(row, 'length', L)
        compare(row, 'original', phase*old)
        compare(row, 'shifted', phase*(old-difference))
        compare(row, 'signed_curvature', phase*difference)
        compare(row, 'signed_coefficient_curvature_fraction', difference/old)
        assert row['endpoints_zero'] and row['whole_mask_completion_asserted'] is False

    result = dict(schema='riesz-saddle-centers-replay-v1', precision_bits=420,
        ball_comparisons=checked, relative_width_checks=width_checks,
        source_rows=len(document['source_rows']), finite_rows=len(document['finite_rows']),
        actual_prime_atoms=len(document['actual_prime_atoms']),
        all_order_joined_pairs=len(document['joined_factorial_pairs']),
        independent_from_producer=True, actual_zeros_sampled=False,
        native_mask_completion_verified=False, arithmetic_floor_verified=False, passed=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
