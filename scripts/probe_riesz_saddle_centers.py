#!/usr/bin/env python3
"""Optional matched two-center experiment, with unchanged finite prime masks.

Source-model ball controls and literal finite prime-atom regressions are
reported separately. Neither is a bound for the native retained carrier.
All factorial orders, original phases, and same-prime diagonals are kept.
This script is not a Lean dependency and is outside ordinary CI.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from flint import acb, arb, ctx, fmpz


def ball(x: arb) -> str:
    return x.str(95, radius=True)


def complex_ball(x: acb) -> list[str]:
    return [ball(x.real), ball(x.imag)]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("data/riesz-saddle-centers-probe.json"))
    args = parser.parse_args()
    ctx.prec = 360
    eta = arb(3)/100
    sources, finite, atoms, joined = [], [], [], []
    for num, den in [(1, 2), (20001, 40000), (10001, 20000)]:
        u = arb(num)/den
        source = 1+(arb(19)/13).log()-(arb(32)/13).log()/(-2*u*u.log())
        attenuation = (-eta**2/(2*u**2)).exp()
        gain = source*(1-attenuation)
        assert attenuation*source < arb(399)/5000
        sources.append(dict(u=[num, den], original=ball(source),
            vertical_attenuation=ball(attenuation), vertical_source=ball(attenuation*source),
            signed_difference_source=ball(gain), headroom=ball(arb(399)/5000-attenuation*source),
            real_shift_source=ball(source/attenuation)))
        for n in [640, 4096, 16384, 65536, 262144]:
            cutoff = fmpz(den)**n//(fmpz(num)**n*(n+1))
            length = 2*arb(cutoff+2).log()
            k = 13*n//32
            a = 1+arb(n-k+1).digamma()-arb(k+1).digamma()
            b = arb(n+2).digamma()-arb(k+1).digamma()
            factor = arb(n+1)/(u*length)
            delta = eta/arb(n+1).sqrt()
            ratio = u/(u**2+delta**2).sqrt()
            original = a-factor*b
            matched = ratio**(n+1)*(a-ratio*factor*b)
            direct_first = sum(ratio**(n+1)/arb(n) for _ in range(n)) if n == 640 else ratio**(n+1)
            assert direct_first.overlaps(ratio**(n+1))
            assert original-matched > 0
            for m in [1, 2]:
                finite.append(dict(u=[num, den], N=n, multiplicity=m, K=k,
                    length=ball(length), delta=ball(delta), radius_ratio=ball(ratio),
                    original=ball(m*m*original), matched=ball(m*m*matched),
                    signed_difference=ball(m*m*(original-matched))))

    # Pinned exact integers copied from the existing proved-prime cache.
    # Retaining the compact input makes this optional probe reproducible
    # without the ignored .lake cache. The
    # controls are below the native N>=65536 regime; no native membership
    # or full prime population is inferred from this finite regression.
    cache = Path('data/riesz-saddle-centers-prime-seeds.json')
    sampled = json.loads(cache.read_text())
    for row in sampled['rows']:
        n = row['N']
        p, q = int(row['p']), int(row['q'])
        assert fmpz(p).is_prime() and fmpz(q).is_prime()
        if p < q:
            p, q = q, p
        x, z = arb(p).log(), arb(q).log()
        u, delta = arb(10001)/20000, eta/arb(n+1).sqrt()
        theta = (delta/u).atan()
        cutoff = fmpz(20000)**n//(fmpz(10001)**n*(n+1))
        length, K = 2*arb(cutoff+2).log(), 13*n//32
        # Existing collected factorial bookkeeping, not a prime-density
        # approximation. Endpoints are included and cancel exactly.
        old_coefficient = arb(0)
        tilted_coefficient = arb(0)
        curvature_coefficient = arb(0)
        for total in [n+1, n+2]:
            for i in range(total+1):
                j = total-i
                low = min(i, j)
                if total == n+1:
                    coefficient = arb(n+1 if K < low else 0)+arb(2*i*j)/n
                else:
                    coefficient = -arb((n+1)*(n+2) if K < low else (n+1)*low)/length
                if i == 0 or j == 0:
                    assert coefficient == 0
                mass = x**i*z**j/arb(fmpz.fac_ui(i)*fmpz.fac_ui(j))
                cos_factor = (theta*(i-j)-delta*(x-z)).cos()
                old_coefficient += coefficient*mass
                tilted_coefficient += coefficient*mass*cos_factor
                curvature_coefficient += coefficient*mass*(1-cos_factor)
        assert (old_coefficient-tilted_coefficient-curvature_coefficient).contains(0)
        for height in [55, 142]:
            phase = (-acb(arb(3)/2, height)*(x+z)).exp()*u**(n+1)/arb(n+1)
            original = phase*old_coefficient
            shifted = phase*tilted_coefficient
            curvature_value = phase*curvature_coefficient
            assert (original-shifted-curvature_value).contains(0)
            joined.append(dict(N=n, p=str(p), q=str(q), height=height, K=K,
                length=ball(length), source_box=row['box'], total_factorial_orders=[n+1, n+2],
                endpoints_zero=True, whole_mask_completion_asserted=False,
                original=complex_ball(original), shifted=complex_ball(shifted),
                signed_curvature=complex_ball(curvature_value),
                signed_coefficient_curvature_fraction=ball(curvature_coefficient/old_coefficient)))
        # Preserve the same finite pair and factorial mask throughout.
        for i in sorted({0, 1, 13*n//32, n//2, n-1, n+1}):
            j = n+1-i
            u, delta = arb(10001)/20000, eta/arb(n+1).sqrt()
            theta = (delta/u).atan()
            mismatch = theta*(i-j)-delta*(x-z)
            multiplier = mismatch.cos()
            for height in [55, 142]:
                s = acb(arb(3)/2, height)
                def kernel(k: int, center: acb, prime_log: arb) -> acb:
                    return prime_log**k/arb(fmpz.fac_ui(k))*(-center*prime_log).exp()
                original = kernel(i, s, x)*kernel(j, s, z)
                left = acb(0, theta*i).exp()*kernel(i, s+acb(0, delta), x)
                right = acb(0, -theta*j).exp()*kernel(j, s-acb(0, delta), z)
                swapped_left = acb(0, -theta*i).exp()*kernel(i, s-acb(0, delta), x)
                swapped_right = acb(0, theta*j).exp()*kernel(j, s+acb(0, delta), z)
                shifted = (left*right+swapped_left*swapped_right)/2
                expected = multiplier*original
                assert (shifted-expected).contains(0)
                curvature = (1-multiplier)*original
                assert (original-shifted-curvature).contains(0)
                assert 1-multiplier >= 0
                atoms.append(dict(N=n, p=str(p), q=str(q), i=i, j=j, height=height,
                    source_box=row['box'], theta=ball(theta), delta=ball(delta),
                    mismatch=ball(mismatch), cosine_multiplier=ball(multiplier),
                    original=complex_ball(original), shifted=complex_ball(shifted),
                    signed_curvature=complex_ball(curvature), primes_proved_by_flint=True,
                    native_core_membership_certified=False))
    report = dict(schema='riesz-saddle-centers-v1', precision_bits=360,
        head=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
        source_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_cache_sha256=hashlib.sha256(cache.read_bytes()).hexdigest(),
        original_prime_cache_sha256=sampled['source_cache_sha256'],
        eta=[3, 100], centers='3/2+i*(y +/- eta/sqrt(N+1))',
        angle='atan(delta/u); exact selected-pole phase matching, asymptotic saddle matching',
        source_model_only=True, proof_dependency=False, ordinary_ci=False,
        independent_floor_proved=False, native_prime_population_enumerated=False,
        source_rows=sources, finite_rows=finite, actual_prime_atoms=atoms,
        joined_factorial_pairs=joined,
        verdict='vertical comparison lowers selected source; exact signed same-mask curvature remains unpaid')
    args.output.parent.mkdir(exist_ok=True, parents=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(dict(source_rows=len(sources), finite_rows=len(finite), actual_prime_atoms=len(atoms),
        all_order_joined_pairs=len(joined),
        curvature_positive=sum(arb(a['signed_curvature'][0]) > 0 for a in atoms),
        curvature_negative=sum(arb(a['signed_curvature'][0]) < 0 for a in atoms),
        output=str(args.output)), indent=2))


if __name__ == '__main__':
    main()
