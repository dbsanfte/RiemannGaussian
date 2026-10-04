#!/usr/bin/env python3
"""Independent optional ball replay: direct binomial masses and joined prefixes."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import arb, ctx, fmpz


def mean_joined(n: int, b: arb, share: arb) -> arb:
    mode = int(float(share.mid())*(n-1))
    p = [arb(0) for _ in range(n)]
    p[mode] = arb(fmpz.bin_uiui(n-1, mode))*share**mode*(1-share)**(n-1-mode)
    for i in range(mode, n-1):
        p[i+1] = p[i]*share/(1-share)*(n-1-i)/(i+1)
    for i in range(mode, 0, -1):
        p[i-1] = p[i]*(1-share)/share*i/(n-i)
    assert sum(p).contains(1)
    k = n*13//32
    # Replay the TWO original slots separately, then join without absolutes.
    central = sum(p[i]/(n-i) for i in range(k,n-k))
    successor = sum(p[i]/(n+1-i) for i in range(n-k+1))
    return n*(1/arb(n)+central-b*successor)


def replay() -> None:
    ctx.prec = 920
    path = Path('data/riesz-multi-height-preflight.json')
    data = json.loads(path.read_text())
    assert data['producer_sha256'] == hashlib.sha256(Path('scripts/probe_riesz_multi_height.py').read_bytes()).hexdigest()
    assert data['seed_sha256'] == hashlib.sha256(Path('data/riesz-saddle-centers-prime-seeds.json').read_bytes()).hexdigest()
    checks = 0
    def check(saved: str, actual: arb) -> None:
        nonlocal checks
        ball = arb(saved)
        assert ball.overlaps(actual)
        assert ball.rel_accuracy_bits() >= 230
        checks += 1
    for row in data['actual_prime_controls']:
        n = row['N']
        primes = [int(p) for p in row['primes']]
        assert all(fmpz(p).is_prime() for p in primes)
        x,z = [arb(p).log() for p in primes]
        turns = row['phase_turns']
        assert turns%2 == 0
        height = turns*arb.pi()/z
        assert height > 54
        u = arb(row['u'][0])/row['u'][1]
        cutoff = fmpz(row['u'][1])**n//(fmpz(row['u'][0])**n*(n+1))
        length = 2*arb(cutoff+2).log()
        b = (n+1)/(u*length)
        share = x/(x+z)
        central = mean_joined(n,b,arb(1)/2)
        off = (mean_joined(n,b,share)+mean_joined(n,b,1-share))/2
        assert central > 0 and off < 0
        phase = turns*arb.pi()*x/z
        small = x/z*(2*x/(x+z))**(n-1)*((arb(3)/2)*(z-x)).exp()*central
        # Equivalent expanded cosine polynomial, including both incidences.
        cp,c2 = phase.cos(),(2*phase).cos()
        minus = 2*small*(3-4*c2+(4*phase).cos())/2 + 2*off*(3-4*cp+c2)
        assert minus < 0
        values = dict(length=length,length_factor=b,share=share,height=height,
            central_native_kernel=central,off_diagonal_native_kernel=off,
            minus_three_height_defect_over_positive_scale=minus,
            plus_polynomial_negative_atom=8*off)
        for key,actual in values.items():
            check(row['values'][key],actual)
        assert not row['literal_core_membership_certified']
    for row in data['safe_shift_necessary_cost']:
        n = row['N'];delta=arb(row['delta'][0])/row['delta'][1]
        cost = (delta*row['total_log']).exp()
        ratio = ((arb(10001)/20000)/(arb(1)/2+delta))**(n-1)
        check(row['necessary_coefficient_mass'],cost)
        check(row['coefficient_mass_times_auxiliary_radius_ratio'],cost*ratio)
        assert cost*ratio > 1
    assert not any(data[key] for key in ['complete_prime_population','actual_zero_ordinates',
        'numerical_floor_proof','global_floor_proved','proof_dependency','ordinary_ci',
        'whole_complete_prime_positivity_disproved','correlation_credit_discarded'])
    report = dict(schema='riesz-multi-height-replay-v1',precision_bits=920,ball_and_width_checks=checks,
        actual_prime_rows=len(data['actual_prime_controls']),
        native_order_rows=sum(r['native_order_reached'] for r in data['actual_prime_controls']),
        input_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        replay_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        finite_prime_preflight_only=True,complete_prime_inequality_disproved=False,
        floor_proved=False,ordinary_ci=False,proof_dependency=False,passed=True)
    Path('data/riesz-multi-height-replay.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))


if __name__ == '__main__':
    replay()
