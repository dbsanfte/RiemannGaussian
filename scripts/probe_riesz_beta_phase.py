#!/usr/bin/env python3
"""Audit factorial-face phase quadrature against a separate ball integral.

The test is E exp(i*k*(3/500)*T*(R-E R)) for the literal upper-face
beta distribution R, with T=(N+1)/u and u=10001/20000. The reference
integrates on a centered interval (sixteen standard deviations by default) using Arb's
analytic quadrature, plus a rigorous beta-mass bound for both exterior
pieces. This is a numerical enclosure for this ONE continuum moment,
not a Lean theorem, packet bound, or actual prime-sum estimate.

Ordinary fixed-node beta quadrature can alias these frequencies badly.
Increasing arithmetic precision alone cannot fix that error. The optional
joined diagnostic imports the same node construction. Keep outside CI.
"""
import argparse
import hashlib
import importlib.metadata
import json
from pathlib import Path
import time
from flint import arb, acb, ctx
from probe_riesz_joined_balls import beta_rule


def run(n, node_counts, harmonics, bits, span=16):
    ctx.prec = bits
    u = arb(10001) / 20000
    T = (n + 1) / u
    h = n // 25 - 1
    a, b = h + 1, n - h + 1
    mu = arb(a) / (a + b)
    sd = (arb(a) * b / ((a + b)**2 * (a + b + 1))).sqrt()
    lognorm = (arb.fac_ui(a+b-1).log() - arb.fac_ui(a-1).log()
               - arb.fac_ui(b-1).log() + sd.log())
    left, right = mu - span*sd, mu + span*sd
    assert 0 < left and right < 1
    # |exp(i*w*(r-mu))|=1 for real r, so omitted mass is an error bound.
    # The incomplete-beta algorithm can return a valid but useless enormous
    # enclosure at excessive precision with these large parameters. Use a
    # separately checked working precision and reject loose enclosures.
    with ctx.workprec(256):
        tail = (left.beta_lower(a, b, regularized=True)
                + (1-right).beta_lower(b, a, regularized=True))
    assert tail.is_finite() and 0 < tail and tail < arb('1e-50')
    rules = {q: beta_rule(a, b, q) for q in node_counts}
    rows = []
    for k in harmonics:
        start = time.monotonic()
        freq = 3*k*T/500

        def integrand(x, analytic):
            r = acb(mu) + sd*x
            # Forward Arb's analyticity flag: ignoring the log branch test
            # would invalidate the certified complex quadrature.
            return (lognorm + (a-1)*r.log(analytic=analytic)
                    + (b-1)*(1-r).log(analytic=analytic)
                    + acb(0, freq*sd)*x).exp()

        with ctx.workprec(256):
            middle = acb.integral(integrand, -span, span,
                                  abs_tol=arb(2)**(-140), rel_tol=arb(2)**(-140),
                                  eval_limit=100000)
        assert (middle.is_finite()
                and middle.real.rad() < arb(2)**(-120)
                and middle.imag.rad() < arb(2)**(-120)), 'Reference enclosure is too wide'
        reference = middle + acb(arb(0, tail.upper()), arb(0, tail.upper()))
        tested = []
        for count, nodes in rules.items():
            value = sum(w*acb(0, freq*(r-mu)).exp() for r, w in nodes)
            tested.append({'nodes': count, 'value': str(value),
                           'absolute_error_enclosure': str(abs(value-reference))})
        row = {'harmonic': k, 'frequency_times_sd': str(freq*sd),
               'reference_enclosure': str(reference), 'quadrature': tested,
               'seconds': time.monotonic()-start}
        rows.append(row)
        print(json.dumps(row), flush=True)
    return {'N': n, 'bits': bits, 'sigma_span': span, 'beta_parameters': [a, b],
            'exterior_mass_bound': str(tail), 'rows': rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=1048576)
    parser.add_argument('--nodes', nargs='+', type=int, default=[12, 64, 128])
    parser.add_argument('--harmonics', nargs='+', type=int, default=[1, 2, 4, 6, 10])
    parser.add_argument('--bits', type=int, default=512)
    parser.add_argument('--sigma-span', type=int, default=16,
                        help='Centered integration half-width in standard deviations')
    parser.add_argument('--output', type=Path, required=True)
    a = parser.parse_args()
    if (a.order < 10000 or min(a.nodes) < 2 or min(a.harmonics) < 1
            or a.bits < 256 or a.sigma_span < 16):
        parser.error('require N>=10000, nodes>=2, positive harmonics, bits>=256, span>=16')
    out = run(a.order, a.nodes, a.harmonics, a.bits, a.sigma_span)
    out['scope'] = ('Ball enclosures of individual beta Fourier moments and fixed-node '
                    'quadrature errors; no complete continuum or prime-sum bound')
    out['versions'] = {name: importlib.metadata.version(name)
                       for name in ('python-flint', 'numpy', 'scipy')}
    sources = [Path(__file__), Path(__file__).with_name('probe_riesz_joined_balls.py')]
    out['source_sha256'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(out, indent=2) + '\n')


if __name__ == '__main__':
    main()
