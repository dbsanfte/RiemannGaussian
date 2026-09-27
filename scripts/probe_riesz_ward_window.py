#!/usr/bin/env python3
"""Optional analytic-model audit of the literal factorial order mask.

This does not evaluate primes, the ordered Euler quotient, or the paired
Fourier integral. It tests whether matching a cofactor to its own
logarithmic derivative, by itself, forces the selected convolution small.
The corresponding no-go is proved independently in Lean. This diagnostic
is not part of ordinary CI and does not touch the running coupled probe.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path


def rectangle(N):
    ja, jb = (21*N+39)//40, 23*N//40
    ha, hb = (N+99)//100-1, N//25-1
    # At these orders the actual ownerOrders and total-order constraints
    # hold throughout the Cartesian box. Check all extreme points.
    for j in (ja, jb):
        for h in (ha, hb):
            assert j < N+2 and 0 <= h < N+2-j
            assert 13*N < 40*(j+h) <= 27*N
            assert 21*N <= 40*j <= 23*N
            assert N <= 100*(h+1) <= 4*N
            assert N+1-j-h >= 2
    high = math.fsum(1/j for j in range(ja, jb+1))
    low = math.fsum(1/(h+1) for h in range(ha, hb+1))
    # The second low leg has a Poisson kernel with mean N/40. Compute
    # each retained probability in log form: no quadrature or sampling.
    mean = N/40
    poisson = math.fsum(math.exp(-mean+h*math.log(mean)-math.lgamma(h+1))
                       for h in range(ha, hb+1))
    return dict(order=N, marked_orders=[ja, jb], least_orders=[ha, hb],
                simple_zero=0.0, reciprocal_pole=high*low,
                poisson_pole=high*poisson)


def paired_pole_model(N):
    """Joint integer-gamma formula, independently of prime transport.

    The toy frequency symbol is
      (c**(-j)-(c+i*x)**(-j))/j
      * (c**(-h)-(c+i*x)**(-h))/h
      * i*x/c**(N+2-j-h), c=1/2.
    Its proposed paired Fourier inverse is the joined CDF below. The
    inversion itself is not a Lean theorem in this slice; the finite
    CDF tail bound is. All calculations here are binary64, not intervals.
    """
    U = 10001/20000
    physical = 20000**N//(10001**N*(N+1))+2
    L = 2*math.log(physical)
    mean = L/2
    ja, jb = (21*N+39)//40, 23*N//40
    ha, hb = (N+99)//100-1, N//25-1
    end = jb+hb-1
    # Start at the largest needed Poisson atom, then recur backwards;
    # starting at exp(-mean) would underflow long before the answer does.
    atoms = [0.0]*(end+1)
    atoms[end] = math.exp(-mean+end*math.log(mean)-math.lgamma(end+1))
    if atoms[end] == 0:
        raise ArithmeticError('requested paired-model order underflows binary64')
    for k in range(end, 0, -1):
        atoms[k-1] = atoms[k]*k/mean
    prefix, total = [], 0.0
    for a in atoms:
        total += a
        prefix.append(total)
    terms = []
    for h in range(ha, hb+1):
        terms.append(math.fsum((prefix[j+h-1]-prefix[j-1]-prefix[h-1])/(j*h)
                              for j in range(ja, jb+1)))
    normalized = (2*U)**(N+1)*2*(N+1)/L*math.fsum(terms)
    return dict(order=N, length_over_order=L/N, normalized=normalized,
                uses_literal_integer_length=True,
                three_tail_formula='Q_(j+h-1)-Q_(j-1)-Q_(h-1)',
                formal_tail_premise=mean >= 11*N/16)


def fourier_checks():
    """Optional independent improper-integral regression; requires SciPy.

    QUADPACK error estimates are diagnostics, not interval certificates.
    """
    from scipy.integrate import quad
    from scipy.special import gammaincc
    rows = []
    for j, h, L in ((5, 2, 20.0), (220, 10, 542.4498255930764)):
        def f(x):
            if x == 0:
                return 0j
            v = .5/(.5+1j*x)
            return (1-v**j)*(1-v**h)/x
        a, ea = quad(lambda x:f(x).real, 0, math.inf, weight='sin',
                     wvar=L, epsabs=2e-11, limit=400, limlst=200)
        b, eb = quad(lambda x:f(x).imag, 0, math.inf, weight='cos',
                     wvar=L, epsabs=2e-11, limit=400, limlst=200)
        value = -(a+b)/math.pi
        closed = float(gammaincc(j+h, L/2)-gammaincc(j, L/2)-gammaincc(h, L/2))
        rows.append(dict(j=j, h=h, length=L, improper_integral=value,
                         gamma_formula=closed, difference=value-closed,
                         quadrature_estimated_error=(ea+eb)/math.pi))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', nargs='+', type=int,
                        default=[400, 640, 1600, 6400, 25600, 102400, 262144])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--fourier-check', action='store_true',
                        help='add optional SciPy improper-integral regressions')
    args = parser.parse_args()
    if min(args.orders) < 400:
        parser.error('this diagnostic requires orders >= 400')
    result = dict(
        scope='Synthetic normalized analytic models, before Fourier integration; not a prime-sum bound.',
        producer_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        arithmetic='IEEE binary64; Lean proves the cofinal 1/20 lower bound independently.',
        formulas=dict(pole='F(s)=1/(1+s); -logDeriv F=F',
                      zero='F(s)=1+s; every cofactor moment of order >=2 is zero',
                      reciprocal_low_leg='a_h=1/(h+1)',
                      poisson_low_leg='a_h=exp(-N/40)*(N/40)^h/h!'),
        formal_result='ZetaRieszWardWindowAudit.not_tendsto_pole_rectangle_norm',
        rows=[rectangle(N) for N in args.orders],
        paired_gamma_model=[paired_pole_model(N) for N in (400,640,1600,6400,25600)],
        paired_model_caveat='The scalar tail estimate is formalized; its Fourier inversion and arithmetic transfer are not.',
        improper_integral_regression=fourier_checks() if args.fourier_check else [],
        predicted_limits=dict(reciprocal_pole=math.log(23/21)*math.log(4),
                              poisson_pole=math.log(23/21)),
        exclusions=['no actual prime measure', 'no Fourier pairing',
                    'no counterexample to decay of the actual arithmetic packet',
                    'no zero-free or RH conclusion'])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'output':str(args.output), 'rows':len(result['rows']),
                      'last':result['rows'][-1]}))


if __name__ == '__main__':
    main()
