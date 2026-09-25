#!/usr/bin/env python3
"""Optional joint-boundary probe, excluded from ordinary CI.

Exact rational tilt checks; binomial marginal exploration; actual finite
prime-label regressions. These are not an estimate of the full prime sum.
The beta/Feynman comparison is a separate unmasked modal model.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.special import logsumexp
from scipy.stats import binom


def ll_prime(exponent):
    """Deterministic Lucas--Lehmer numerical check, not a Lean certificate."""
    p, state = (1 << exponent)-1, 4
    for _ in range(exponent-2):
        state = (state*state-2) % p
    assert state == 0
    return p


def literal_label(n_order, exponents):
    primes = [ll_prime(e) for e in exponents]
    logs = [mp.log(p) for p in primes]
    total = mp.fsum(logs)
    shares = [x/total for x in logs]
    u, height = mp.mpf(10001)/20000, mp.mpf(55)
    physical = 20000**n_order//(10001**n_order*(n_order+1))+2
    length = 2*mp.log(physical)
    assert mp.mpf(39)*n_order/20 < total <= mp.mpf(203)*n_order/100
    assert all(n_order*n_order < p < physical*physical for p in primes)
    assert mp.mpf(3)/250 <= min(shares) <= mp.mpf(7)/250
    assert max(shares) < mp.mpf(13)/20
    m = n_order+1
    lf = [mp.loggamma(k+1) for k in range(m+1)]
    r = min(range(3), key=lambda i: primes[i])
    owner = max(range(3), key=lambda i: primes[i])
    weights = []
    for p in range(3):
        if p == r:
            weights.append(mp.mpf(0))
            continue
        other = next(i for i in range(3) if i not in (r, p))
        terms = []
        for j in range((21*n_order+39)//40, 23*n_order//40+1):
            for h in range(max(0, (n_order+99)//100-1), n_order//25):
                k = m-j-h
                if k < 0 or not (13*n_order < 40*(j+h) <= 27*n_order):
                    continue
                terms.append(mp.exp(lf[m]-lf[j]-lf[h]-lf[k]+
                                    j*mp.log(shares[p])+h*mp.log(shares[r])+
                                    k*mp.log(shares[other])))
        weights.append(mp.fsum(terms))
    wrong = mp.fsum(w for i, w in enumerate(weights) if i != owner)
    assert wrong <= 166*mp.exp(-mp.mpf(n_order)/1600)
    assert mp.fsum(weights) <= 1
    riesz = mp.fsum((-1)**mask.bit_count()*max(mp.mpf(0), length-
        mp.fsum(logs[i] for i in range(3) if mask & (1 << i))) for mask in range(8))
    unpaid = [k for k in range(m+1) if k <= 13*n_order//32 and 5*(m-k) < 4*n_order]
    allocated = mp.fsum(mp.binomial(m, k)*(1-x)**k*x**(m-k)
                       for x in shares for k in unpaid)
    coefficient = -(1-allocated)*total*riesz/length
    s = mp.mpf(3)/2+1j*height
    kernel = mp.exp(n_order*mp.log(total)-lf[n_order]-s*total)
    original = u**(n_order+1)*weights[owner]*coefficient*kernel
    marked = u**(n_order+1)*mp.fsum(weights)*coefficient*kernel
    correction = u**(n_order+1)*wrong*coefficient*kernel
    ledger_error = abs(marked-original-correction)/max(abs(marked), mp.mpf('1e-10000'))
    assert ledger_error < mp.mpf('1e-65')
    d = [0, 0, 0]
    d[owner], d[r] = 11*n_order//20, n_order//50
    other = next(i for i in range(3) if i not in (r, owner))
    d[other] = m-d[owner]-d[r]
    aw = mp.exp(lf[m]-mp.fsum(lf[k] for k in d)+
                mp.fsum(k*mp.log(x) for k, x in zip(d, shares)))
    prime_product = mp.fprod(mp.exp(k*mp.log(logp)-lf[k]-s*logp)
                            for k, logp in zip(d, logs))
    product_error = abs(aw*kernel-m/total*prime_product)/abs(aw*kernel)
    assert product_error < mp.mpf('1e-65')
    return {
        'N': n_order, 'mersenne_exponents': exponents,
        'log_n_over_N': mp.nstr(total/n_order, 22),
        'shares': [mp.nstr(x, 22) for x in shares],
        'canonical_rectangle_mass': mp.nstr(weights[owner], 22),
        'wrong_owner_rectangle_mass': mp.nstr(wrong, 22),
        'old_allocated_fraction': mp.nstr(allocated, 22),
        'riesz_coefficient': mp.nstr(coefficient, 22),
        'log10_source_normalized_atom': mp.nstr(mp.log10(abs(original)), 22),
        'complex_ledger_relative_error': mp.nstr(ledger_error, 8),
        'prime_kernel_relative_error': mp.nstr(product_error, 8),
        'scope': 'individual actual-prime label; not an exhaustive carrier evaluation',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    mp.mp.dps = 100
    certificates = []
    for a, m, b, q in [(21, 40, Q(21,20), Q(11,10)), (29,50,Q(47,50),Q(9,10))]:
        assert b**m/q**a <= 1-Q(m,1600)
        certificates.append({'a': a, 'm': m, 'base': str(b), 'tilt': str(q),
                             'power_inequality': True})
    u, tilt = mp.mpf(10001)/20000, mp.mpf(131071)/262144
    rate = u/tilt*mp.exp(-mp.mpf(1)/1600)
    marginal_rows = []
    for n in (256,640,1536,4096,8192,65536,262144):
        js = np.arange((21*n+39)//40, 23*n//40+1)
        row = {'N': n}
        for name, x in [('lower_exterior',.5),('upper_exterior',.6),('old_lower_edge',43/80),
                        ('old_upper_edge',9/16),('interior',.55)]:
            row[name+'_log10_mass'] = float(logsumexp(binom.logpmf(js,n+1,x))/np.log(10))
        row['normalized_exterior_bound_log10_excluding_majorant'] = mp.nstr(
            mp.log10(2*u)+n*mp.log10(rate), 20)
        marginal_rows.append(row)
    labels = [literal_label(400,[607,521,31]), literal_label(400,[607,521,19]),
              literal_label(1600,[2281,2203,127])]
    # Euler's beta / Feynman identity is a MODEL diagnostic. It uses a
    # complete share interval and radial moment, not any literal Riesz mask.
    # Small-order quadrature checks the formula; high-order bounds come from
    # its exact product expression, with no oscillatory quadrature claim.
    beta_checks, modal_rates = [], []
    for edge in (mp.mpf(43)/80,mp.mpf(21)/40,mp.mpf(1)/2,mp.mpf(3)/5):
        left, right = mp.mpc('.5',55), mp.mpc('.5',55*(1-1/edge))
        m, j = 4, 2
        value = mp.quad(lambda x: mp.binomial(m,j)*x**j*(1-x)**(m-j)/
                        (x*right+(1-x)*left)**(m+2), [0,edge,1])
        exact = 1/((m+1)*right**(j+1)*left**(m-j+1))
        error = abs(value-exact)/abs(exact)
        assert error < mp.mpf('1e-60')
        beta_checks.append({'resonant_share':mp.nstr(edge), 'relative_error':mp.nstr(error,8)})
        modal_rates.append({'resonant_share':mp.nstr(edge),
                            'unmasked_product_rate_upper':mp.nstr(u/min(abs(left),abs(right)),22)})
    result = {
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'status':'exploratory; Lean supplies the arithmetic bounds; no signed floor or zero exclusion',
        'rate':mp.nstr(rate,35), 'exact_rational_tilt_checks':certificates,
        'marginals':marginal_rows, 'literal_labels':labels,
        'unmasked_beta_model_checks':beta_checks, 'unmasked_modal_rates':modal_rates,
        'beta_reference':'https://dlmf.nist.gov/15.6.E1',
        'limits':['No prime-density or completed-mode transport is inferred.',
                  'The beta model omits the least-share, Riesz, allocation and finite radial masks.',
                  'The actual-prime samples do not evaluate the signed sum over all labels.'],
    }
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'rate':result['rate'],'labels':labels,'modal_rates':modal_rates},indent=2))


if __name__ == '__main__':
    main()
