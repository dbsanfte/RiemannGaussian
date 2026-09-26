#!/usr/bin/env python3
"""Optional independent radial Fourier-moment audit for the coupled model.

Integrate the finite-window factorial density using the integer incomplete
gamma identity, with an explicit decreasing-ratio remainder. This is a
single exponential moment audit, NOT a bound for the varying-amplitude
coupled expression, a Lean certificate, or an arithmetic prime sum.
"""
import argparse
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx
from probe_riesz_joined_balls import legendre
from riesz_radial_gamma import gamma_rule


def integer_gamma_tail(n, z, tolerance):
    """Q(n+1,z)=exp(-z)*sum_(k=0)^n z^k/k!, with a paid small tail.

    Sum backwards from k=n. After k<|z|, all subsequent ratios have
    modulus <=k/|z|. Retain the full complex sum before paying this tail.
    """
    assert z.real > 0
    term = (-z+n*z.log()-arb.fac_ui(n).log()).exp()
    value, k = term, n
    size = abs(z)
    while k:
        term *= k/z
        value += term
        k -= 1
        if k < size:
            bound = (abs(term)*k/(size-k)).upper()
            if bound < tolerance:
                value += acb(arb(0, bound), arb(0, bound))
                break
    assert value.is_finite()
    return value, n-k+1


def radial_reference(n, u, lo, hi, growth, frequency):
    a = acb(u-growth, -frequency)
    low, ilow = integer_gamma_tail(n, a*lo, arb(2)**(-800))
    high, ihigh = integer_gamma_tail(n, a*hi, arb(2)**(-800))
    answer = (acb(u)/a)**(n+1)*(low-high)
    assert answer.is_finite() and abs(answer.real.rad()+answer.imag.rad()) < arb('1e-60')
    return answer, [ilow, ihigh]


def gamma_checks():
    """Compare with a separate implementation where its complex path works."""
    checks = 0
    for n in [0, 1, 5, 64, 200]:
        for z in [acb(3, 2), acb(10, -7), acb(100, 3)]:
            value, _ = integer_gamma_tail(n, z, arb(2)**(-800))
            reference = z.gamma_upper(n+1, regularized=True)
            assert reference.is_finite() and value.overlaps(reference)
            checks += 1
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=65536)
    parser.add_argument('--nodes', type=int, nargs='+', default=[12, 24, 48, 96])
    parser.add_argument('--gamma-nodes', type=int, nargs='+', default=[12, 16, 24, 32])
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.order < 10000 or min(args.nodes+args.gamma_nodes) < 2:
        parser.error('require N>=10000 and node counts>=2')
    ctx.prec = 1024
    names = [Path(__file__).name, 'probe_riesz_joined_balls.py', 'riesz_radial_gamma.py']
    hashes = lambda: {p: hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest()
                      for p in names}
    frozen = hashes()
    regression_count = gamma_checks()
    n = args.order
    u, lo, hi = arb(10001)/20000, arb(39)*n/20, arb(203)*n/100
    logfac = arb.fac_ui(n).log()
    rules = {q: [(t, w*((n+1)*u.log()-u*t+n*t.log()-logfac).exp())
                 for t, w in legendre(q, lo, hi)] for q in args.nodes}
    with ctx.workprec(4096):
        gamma_rules = {q: gamma_rule(n, arb(10001)/20000, arb(39)*n/20, arb(203)*n/100, q)
                       for q in args.gamma_nodes}
    rows = []
    for freq_text in ['0', '3/1000', '3/500']:
        f = arb(freq_text)
        for growth_text in ['0', '1/40000']:
            g = arb(growth_text)
            reference, terms = radial_reference(n, u, lo, hi, g, f)
            if f == 0:
                a = u-g
                independent = (u/a)**(n+1)*((a*lo).gamma_upper(n+1, regularized=True)
                                                   -(a*hi).gamma_upper(n+1, regularized=True))
                assert reference.imag.contains(0) and reference.real.overlaps(independent)
            values = []
            for q, rule in rules.items():
                value = sum(w*acb(g*t, f*t).exp() for t, w in rule)
                values.append(dict(nodes=q, value=str(value), norm_error=str(abs(value-reference))))
            weighted = []
            for q, (rule, audit) in gamma_rules.items():
                value = sum(w*acb(g*t, f*t).exp() for t, w in rule)
                weighted.append(dict(nodes=q, value=str(value), norm_error=str(abs(value-reference)),
                                     centered_moment_checks=audit['moment_checks']))
            rows.append(dict(frequency=freq_text, growth=growth_text,
                             reference_enclosure=str(reference), reference_norm=str(abs(reference)),
                             gamma_terms=terms, quadrature=values,
                             gamma_weighted_quadrature=weighted))
    assert hashes() == frozen
    out = dict(N=n, radial_interval=['39N/20', '203N/100'],
               density='u^(N+1)*exp(-u*T)*T^N/N!, u=10001/20000',
               rows=rows, source_sha256=frozen, independent_gamma_checks=regression_count,
               scope='Single radial exponential moments with paid finite-sum remainder; '
                     'not a varying-amplitude quadrature bound, continuum packet enclosure, '
                     'Lean theorem or arithmetic estimate. Outside ordinary CI.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    for r in rows:
        print(r['frequency'], r['growth'],
              [(v['nodes'], float(arb(v['norm_error']).upper())) for v in r['quadrature']])
        print('gamma-weighted', [(v['nodes'], float(arb(v['norm_error']).upper()))
                                 for v in r['gamma_weighted_quadrature']])


if __name__ == '__main__':
    main()
