#!/usr/bin/env python3
"""Optional algebra/source preflight; never a complete-prime floor certificate.

Collect the native factorial coefficient BEFORE applying a trigonometric
polynomial. Exact primes, full phases, diagonals and both factorial prefixes
are retained. Ball controls also reach native order 65536.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

from flint import arb, ctx, fmpz


def expectation(n: int, b: arb, q: arb) -> arb:
    """Exact binomial polynomial, evaluated by rescaled positive recurrence."""
    mode = int(float(q.mid())*(n-1))
    probability = [arb(0) for _ in range(n)]
    probability[mode] = arb(1)
    for i in range(mode, n-1):
        probability[i+1] = probability[i]*(n-1-i)/(i+1)*q/(1-q)
    for i in range(mode, 0, -1):
        probability[i-1] = probability[i]*i/(n-i)*(1-q)/q
    k = 13*n//32
    def joined(i: int) -> arb:
        return (1/arb(n)+(1/arb(n-i) if k <= i < n-k else arb(0))
                -(b/arb(n+1-i) if i <= n-k else arb(0)))
    weights = [(joined(i)+joined(n-1-i))/2 for i in range(n)]
    return n*sum(w*p for w, p in zip(weights, probability))/sum(probability)


def main() -> None:
    ctx.prec = 768
    seed_path = Path('data/riesz-saddle-centers-prime-seeds.json')
    seed = json.loads(seed_path.read_text())['rows'][2]
    large_primes = sorted([int(seed['p']),int(seed['q'])])
    controls = [(n,[2,3],20) for n in [256,640,4096,65536]]
    controls += [(n,large_primes,8192) for n in [4096,65536]]
    rows = []
    for n,primes,turns in controls:
        assert all(fmpz(p).is_prime() for p in primes)
        assert turns%2 == 0
        x,z = [arb(p).log() for p in primes]
        share = x/(x+z)
        # The larger-prime diagonal has EXACT phase 2*turns*pi.
        y = turns*arb.pi()/z
        assert y > 54
        phase = turns*arb.pi()*x/z
        u = arb(10001)/20000
        cutoff = fmpz(20000)**n//(fmpz(10001)**n*(n+1))
        length = 2*arb(cutoff+2).log()
        b = (n+1)/(u*length)
        central = expectation(n, b, arb(1)/2)
        off_diagonal = expectation(n, b, share)
        assert central > 0 and off_diagonal < 0
        # Divide by the positive common scale
        # u^(N+1)*x*z*T^(N-1)/(N-1)!*6^(-3/2)/N.
        small_diagonal = x/z*(2*x/(x+z))**(n-1)*(arb(primes[1])/primes[0])**(arb(3)/2)*central
        # Both ordered 2,3 incidences; 3,3 diagonal identically zero here.
        minus_test = (2*small_diagonal*(1-(2*phase).cos())**2+
                      4*off_diagonal*(1-phase.cos())**2)
        assert minus_test < 0
        # At y=0 the plus polynomial is 8, so the negative atom stays negative.
        plus_atom = 8*off_diagonal
        assert plus_atom < 0
        values = dict(length=length,length_factor=b,share=share,height=y,
                      central_native_kernel=central,off_diagonal_native_kernel=off_diagonal,
                      minus_three_height_defect_over_positive_scale=minus_test,
                      plus_polynomial_negative_atom=plus_atom)
        rows.append(dict(N=n,u=[10001,20000],primes=[str(p) for p in primes],phase_turns=turns,
                         height_definition='phase_turns*pi/log(larger_prime)',
                         native_order_reached=n>=65536,
                         literal_core_membership_certified=False,
                         values={key:value.str(80,radius=True) for key,value in values.items()}))
        print(json.dumps(dict(N=n,central=float(central.mid()),off_diagonal=float(off_diagonal.mid()),
                              minus_defect=float(minus_test.mid()))),flush=True)
    shift = arb(1)/10000
    shift_rows = []
    for n in [65536, 1000000, 10000000]:
        # A phase-zero test already requires auxiliary coefficient l1 mass
        # >= exp(delta*T). This is an exact necessary pointwise condition.
        necessary_mass = (shift*(2*n)).exp()
        decay = ((arb(10001)/20000)/(arb(1)/2+shift))**(n-1)
        shift_rows.append(dict(N=n,delta=[1,10000],total_log=2*n,
            necessary_coefficient_mass=necessary_mass.str(80,radius=True),
            coefficient_mass_times_auxiliary_radius_ratio=(necessary_mass*decay).str(80,radius=True)))
    result = dict(schema='riesz-multi-height-preflight-v1',precision_bits=768,
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        seed_sha256=hashlib.sha256(seed_path.read_bytes()).hexdigest(),
        actual_prime_controls=rows,safe_shift_necessary_cost=shift_rows,
        exact_pair_bookkeeping=True,correlation_credit_discarded=False,
        whole_complete_prime_positivity_disproved=False,
        complete_prime_population=False,actual_zero_ordinates=False,
        numerical_floor_proof=False,global_floor_proved=False,proof_dependency=False,ordinary_ci=False,
        verdict='Native collected pair kernel changes sign. The unsigned three-height square cannot be applied unchanged. The upper-bound minus square fails even on the finite actual prime set {2,3}, including both incidences and diagonals. This does not disprove a complete-prime inequality exploiting additional global prime correlations. All-safe auxiliary shifts fail the pointwise tail test; their necessary growing costs offset their proposed radius saving.')
    Path('data/riesz-multi-height-preflight.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__ == '__main__':
    main()
