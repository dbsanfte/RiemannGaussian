#!/usr/bin/env python3
"""Optional coupled CONTINUOUS finite-mode Riesz diagnostic.

Use the original two beta faces, owner-order band, moving length, radial
core interval and conjugate modes. Evaluate the entire continuous count
response before taking the outer quadrature: no cutoff lattice and no
split-head interpolation. Balls cover continuous-response evaluation,
input-node enclosures and explicitly skipped negligible numerical terms.
They DO NOT cover the outer quadrature error or transfer to ordinary primes.

Count classes above the literal model caps 55/13 have a separate simplex
allowance. Numerical exterior budgets are not theorems about arithmetic
labels. Keep outside ordinary CI and certificate verification.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor
import hashlib
import importlib.metadata
import json
import math
import multiprocessing
from pathlib import Path
import time

from flint import acb, arb, ctx, fmpz
from probe_riesz_joined_balls import beta_rule, legendre
from probe_riesz_continuous_balls import ContinuousCascade, ball
from riesz_continuous_projection import compress_model, count_allowance, response_interval
from riesz_binomial_balls import binomial_tail


def sources():
    root = Path(__file__).parent
    return {name: hashlib.sha256((root/name).read_bytes()).hexdigest() for name in
            (Path(__file__).name, 'probe_riesz_continuous_balls.py',
             'riesz_continuous_projection.py', 'riesz_binomial_balls.py',
             'probe_riesz_joined_balls.py', 'requirements-riesz-balls.txt')}


def task(key):
    it, face, ir = key
    started = time.monotonic()
    T, wt = TS[it]
    r, wr = RS[face][ir]
    lam = LENGTH/T
    assert r > 0 and r < arb(1)/3 and lam > arb(3)/5 and lam < 1
    cap = 54 if face == 0 else 12
    smax = arb(1)/(2*r)
    dmax = (lam-arb(1)/2)/r
    growth_max = (T/80000).exp()
    owner_max = 1+6*(3*T/200000).exp()
    coefficients = CONDITIONALS[face][ir]
    marginal_norm = sum(abs(pw*c) for (_, pw), c in zip(PS, coefficients))
    full_allowance = count_allowance(smax, dmax).upper()
    common = owner_max*growth_max*2/lam
    row_bound = (marginal_norm*common*full_allowance).upper()
    weight = wt*wr
    if abs(weight)*row_bound < SKIP_BUDGET:
        return dict(key=key, value=str(ball(arb(0), row_bound)),
                    count_tail=str(row_bound), skipped_owner_nodes=len(PS),
                    response_evaluations=0, maximum_integrand=0.,
                    seconds=time.monotonic()-started)
    scale = T*r
    nodes = [acb(-scale/40000), acb(0, 3*scale/500), acb(0, -3*scale/500)]
    end = math.ceil(float(smax.upper()))+1
    assert smax < end
    model = ContinuousCascade(nodes, [1, 3, 3], end, SUBDIVISION, DEGREE)
    if COMPRESSION > 0:
        compress_model(model, COMPRESSION)
    total, tail, skipped_error = arb(0), arb(0), arb(0)
    skipped, largest = 0, 0.
    for (p, pw), conditional in zip(PS, coefficients):
        s, d = (1-p)/r, (lam-p)/r
        growth = (T*(1-p)/40000).exp()
        owner = 1+6*(T*p/40000).exp()*(3*T*p/500).cos()
        factor = pw*conditional*owner*growth/(p*lam)
        bound = (abs(factor)*full_allowance).upper()
        if abs(weight)*bound < SKIP_BUDGET/len(PS):
            skipped_error += bound
            tail += bound
            skipped += 1
            continue
        with ctx.workprec(PROJECTION_BITS):
            value = response_interval(model, s, d,
                negligible=lambda bound: abs(weight*factor)*bound < SKIP_BUDGET/len(PS))
        assert value.is_finite()
        total += factor*value
        tail += abs(factor)*count_allowance(s, d, cap+1)
        largest = max(largest, float(abs(conditional*owner*growth*value/(p*lam)).upper()))
    return dict(key=key, value=str(ball(total, skipped_error)), count_tail=str(tail),
                skipped_owner_nodes=skipped, response_evaluations=len(PS)-skipped,
                norm_enclosed_points=getattr(model, 'norm_enclosed_points', 0),
                maximum_integrand=largest, seconds=time.monotonic()-started)


def prepare(n, tn, rn, pn, subdivision, degree, bits, tolerance,
            compression=arb(0), projection_bits=None):
    global TS, RS, PS, LENGTH, CONDITIONALS, SUBDIVISION, DEGREE, SKIP_BUDGET
    global COMPRESSION, PROJECTION_BITS
    start = time.monotonic()
    ctx.prec = bits
    ctx.threads = 1
    u = arb(10001)/20000
    X = (fmpz(20000)**n)//((fmpz(10001)**n)*(n+1))+2
    LENGTH = 2*arb(X).log()
    TS = []
    for t, w in legendre(tn, arb(39)*n/20, arb(203)*n/100):
        logpdf = (n+1)*u.log()-u*t+n*t.log()-arb.fac_ui(n).log()
        TS.append((t, w*logpdf.exp()))
    hs = [(n+99)//100-2, n//25-1]
    RS = [beta_rule(h+1, n-h+1, rn) for h in hs]
    PS = legendre(pn, arb(1)/2, arb(3)/5)
    jlo, jhi = (21*n+39)//40, 23*n//40
    marginals = [binomial_tail(p, n+1, jlo)-binomial_tail(p, n+1, jhi+1) for p, _ in PS]
    CONDITIONALS, residuals = [], []
    for f, h in enumerate(hs):
        rows = [[binomial_tail(p/(1-r), n-h, jlo)-binomial_tail(p/(1-r), n-h, jhi+1)
                 for p, _ in PS] for r, _ in RS[f]]
        observed = [sum(w*row[ip] for (_, w), row in zip(RS[f], rows)) for ip in range(pn)]
        correction = [m/v if v > arb(2)**(-180) else arb(1) for m, v in zip(marginals, observed)]
        CONDITIONALS.append([[c*correction[ip] for ip, c in enumerate(row)] for row in rows])
        residuals.append(str(max(abs(v-m) for v, m in zip(observed, marginals))))
    SUBDIVISION, DEGREE = subdivision, degree
    COMPRESSION, PROJECTION_BITS = arb(compression), projection_bits or bits
    SKIP_BUDGET = arb(tolerance)/(tn*rn*2)
    return dict(rule_setup_seconds=time.monotonic()-start,
                radial_mass=str(sum(w for _, w in TS)),
                owner_marginal_error_before_calibration=residuals)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=65536)
    parser.add_argument('--tnodes', type=int, default=48)
    parser.add_argument('--rnodes', type=int, default=128)
    parser.add_argument('--pnodes', type=int, default=256)
    parser.add_argument('--subdivision', type=int, default=4)
    parser.add_argument('--degree', type=int, default=128)
    parser.add_argument('--bits', type=int, default=768)
    parser.add_argument('--workers', type=int, default=4)
    parser.add_argument('--skip-budget', default='1e-20')
    parser.add_argument('--max-radius', default='1e-18')
    parser.add_argument('--compression', default='1e-45', help='Paid uniform Taylor tail per completed cell')
    parser.add_argument('--projection-bits', type=int, default=256)
    parser.add_argument('--benchmark', action='store_true', help='Evaluate one central row on each face')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if (args.order < 10000 or min(args.tnodes, args.rnodes, args.pnodes) < 2
            or args.workers < 1 or args.degree < 32 or args.bits < 256):
        parser.error('invalid order, node count, degree, workers or precision')
    if not 0 < arb(args.skip_budget) < 1 or not 0 < arb(args.max_radius) < 1:
        parser.error('require budgets between zero and one')
    if not 0 <= arb(args.compression) < 1 or not 128 <= args.projection_bits <= args.bits:
        parser.error('require 0<=compression<1 and 128<=projection-bits<=bits')
    started = time.monotonic()
    frozen = sources()
    setup = prepare(args.order, args.tnodes, args.rnodes, args.pnodes,
                    args.subdivision, args.degree, args.bits, args.skip_budget,
                    args.compression, args.projection_bits)
    print('setup', json.dumps(setup), flush=True)
    keys = [(it, f, ir) for it in range(args.tnodes) for f in range(2) for ir in range(args.rnodes)]
    if args.benchmark:
        keys = [(args.tnodes//2, f, args.rnodes//2) for f in range(2)]
    fronts, tails = [arb(0), arb(0)], [arb(0), arb(0)]
    counts, maxima = [0, 0], [0., 0.]
    skipped = [0, 0]
    norm_enclosed = [0, 0]
    audit_rows = []
    args.output.parent.mkdir(parents=True, exist_ok=True)
    checkpoint = args.output.with_suffix('.rows.jsonl')
    # Row records preserve an expensive run's evidence, not a resume signal.
    with checkpoint.open('w') as log, ProcessPoolExecutor(
            max_workers=args.workers, mp_context=multiprocessing.get_context('fork')) as pool:
        log.write(json.dumps({'source_sha256': frozen, 'arguments': {k: str(v) if isinstance(v, Path) else v
                                                                    for k, v in vars(args).items()}})+'\n')
        log.flush()
        for done, row in enumerate(pool.map(task, keys, chunksize=1), 1):
            it, f, ir = row['key']
            weight = TS[it][1]*RS[f][ir][1]
            fronts[f] += weight*arb(row['value'])
            tails[f] += abs(weight)*arb(row['count_tail'])
            counts[f] += row['response_evaluations']
            skipped[f] += row['skipped_owner_nodes']
            norm_enclosed[f] += row.get('norm_enclosed_points', 0)
            maxima[f] = max(maxima[f], row['maximum_integrand'])
            log.write(json.dumps(row)+'\n')
            log.flush()
            if args.benchmark:
                audit_rows.append(row)
            if done % 16 == 0 or args.benchmark:
                print('progress', done, len(keys), 'sec', time.monotonic()-started, flush=True)
    assert sources() == frozen, 'Input changed during computation'
    joined = fronts[0]-fronts[1]
    assert joined.is_finite() and joined.rad() < arb(args.max_radius), 'Final ball too wide'
    out = dict(N=args.order, tnodes=args.tnodes, rnodes=args.rnodes, pnodes=args.pnodes,
               subdivision=args.subdivision, degree=args.degree, bits=args.bits,
               compression=args.compression, projection_bits=args.projection_bits,
               benchmark_only=args.benchmark, fronts=[str(v) for v in fronts],
               joined=str(joined), omitted_model_count_allowance=[str(v) for v in tails],
               response_evaluations=counts, skipped_owner_nodes=skipped,
               norm_enclosed_points=norm_enclosed,
               skip_budget=args.skip_budget, maximum_integrand=maxima,
               setup=setup, seconds=time.monotonic()-started, source_sha256=frozen,
               audit_rows=audit_rows,
               versions={p: importlib.metadata.version(p) for p in ('python-flint', 'numpy', 'scipy')},
               scope='Continuous all-count response evaluated before finite outer quadrature. '
                     'Response, roundoff and numerical skipping errors enclosed; outer quadrature '
                     'error and arithmetic transport are NOT enclosed. No prime-sum bound or '
                     'asymptotic conclusion. A benchmark-only run is not the coupled sum.')
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out), flush=True)


if __name__ == '__main__':
    main()
