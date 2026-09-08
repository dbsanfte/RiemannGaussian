"""Compare complete logarithmic eta moments for five gamma smoothing orders.

The integral is centered by eta(s) Q_k(x) away from zeros. At numerical
zero samples this centering vanishes to numerical precision. Independent
integrated Taylor and incomplete-gamma expansions are compared with the
eta derivative. Truncation comparisons are numerical checks, not certified
remainder estimates. No Mobius bound or zero bound is inferred.
"""
import argparse
import json
from pathlib import Path
import mpmath as mp

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', default='/tmp/eta-gamma-log-mode.json')
args = parser.parse_args()
mp.mp.dps = 80
orders = [1, 2, 3, 4, 6]
terms = 210
limit = 240

def pair(z):
    return [mp.nstr(z.real, 40), mp.nstr(z.imag, 40)]

def eta(s):
    return (1 - mp.power(2, 1-s)) * mp.zeta(s)

records = []
for zero_index in [1, 2, 3]:
    z = mp.zetazero(zero_index)
    for sigma in [mp.mpf('0.5'), mp.mpf('0.75')]:
        s = mp.mpc(sigma,z.imag)
        e0 = eta(s)
        derivative = mp.diff(eta,s)
        shifted = [eta(s-n) - e0 for n in range(terms+1)]
        coeffs = [(-1)**(q+1)*mp.power(q,-s) for q in range(1,limit+1)]
        for order in orders:
            def low_part(nmax):
                return mp.fsum(
                    (-1)**(n+order-1)*mp.binomial(n-1,order-1)*shifted[n]
                    / (mp.factorial(n)*n) for n in range(order,nmax+1)
                )
            low = low_part(terms)
            low_short = low_part(terms-30)
            def tail_kernel(q):
                return mp.e1(q) + mp.fsum(mp.gammainc(j,q,mp.inf)/mp.factorial(j)
                                            for j in range(1,order))
            tails = [c*tail_kernel(q) for q,c in enumerate(coeffs,1)]
            high = mp.fsum(tails)-e0*tail_kernel(1)
            high_short = mp.fsum(tails[:-30])-e0*tail_kernel(1)
            integral = low+high
            discrepancy = abs(integral-derivative)
            assert discrepancy < mp.mpf('1e-55'), (zero_index,sigma,order,discrepancy)
            truncation_difference = abs(low-low_short)+abs(high-high_short)
            assert truncation_difference < mp.mpf('1e-55'), (zero_index,sigma,order,truncation_difference)
            record = dict(zero_index=zero_index,s=pair(s),order=order,
                          sample_is_numerical_zero=(sigma==mp.mpf('0.5')),
                          eta_absolute=mp.nstr(abs(e0),12),
                          centered_integral=pair(integral),eta_derivative=pair(derivative),
                          discrepancy=mp.nstr(discrepancy,12),
                          low_integral=pair(low),high_integral=pair(high),
                          truncation_comparison=mp.nstr(abs(low-low_short)+abs(high-high_short),12))
            records.append(record)
            print(json.dumps(record),flush=True)
Path(args.output).write_text(json.dumps(dict(
    status='Numerical cross-check only. No zero bound or Mobius estimate.',
    centered_definition='G_s,k(x) - eta(s) Q_k(x); unchanged at actual zeros',
    methods='Integrated Taylor expansion on (0,1), independent incomplete-gamma sums on (1,infinity)',
    records=records),indent=2)+'\n')
