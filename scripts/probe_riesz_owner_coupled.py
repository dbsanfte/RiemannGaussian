#!/usr/bin/env python3
"""Optional coupled model using the exact conditional owner-order measure.

The positive approximate rule has independently audited polynomial moments.
It replaces only outer quadrature: the continuous count response, both beta
faces, moving length, radial window and owner share mask remain. In
particular p=(1-r)*x is retained at every node. No marginal calibration.
There is still NO complete outer-quadrature or arithmetic error estimate.
"""
import hashlib
from pathlib import Path
import time

from flint import arb, ctx, fmpz
import probe_riesz_joined_continuous_balls as coupled
from probe_riesz_joined_balls import beta_rule
from riesz_owner_gauss import owner_rule
from riesz_radial_gamma import gamma_rule


OWNER_ROWS = []
ORIGINAL_TASK = coupled.task
ORIGINAL_SOURCES = coupled.sources


def prepare(n, tn, rn, pn, subdivision, degree, bits, tolerance,
            compression=arb(0), projection_bits=None):
    global OWNER_ROWS
    started = time.monotonic()
    ctx.prec, ctx.threads = bits, 1
    u = arb(10001)/20000
    cutoff = (fmpz(20000)**n)//((fmpz(10001)**n)*(n+1))+2
    coupled.LENGTH = 2*arb(cutoff).log()
    with ctx.workprec(max(4096, bits)):
        coupled.TS, radial_audit = gamma_rule(n, arb(10001)/20000,
                                            arb(39)*n/20, arb(203)*n/100, tn)
    hs = [(n+99)//100-2, n//25-1]
    coupled.RS = [beta_rule(h+1, n-h+1, rn) for h in hs]
    lo, hi = (21*n+39)//40, 23*n//40
    bases, audits = [], []
    with ctx.workprec(max(bits, 32*pn, 4096)):
        for h in hs:
            base, audit = owner_rule(n-h, lo, hi, pn)
            bases.append(base)
            audits.append(audit)
    OWNER_ROWS, coupled.CONDITIONALS, removed = [], [], []
    for face, base in enumerate(bases):
        rows, conditions, lost = [], [], []
        for r, _ in coupled.RS[face]:
            selected = []
            for x, w in base:
                p = (1-r)*x
                if arb(1)/2 < p and p < arb(3)/5:
                    selected.append((p, w))
                else:
                    assert p <= arb(1)/2 or arb(3)/5 <= p, 'Unresolved owner-mask boundary'
            assert selected
            rows.append(selected)
            # The measure already contains the original 1/p. Cancel the
            # old task's denominator exactly, without fitting its marginal.
            conditions.append([p for p, _ in selected])
            lost.append(pn-len(selected))
        OWNER_ROWS.append(rows)
        coupled.CONDITIONALS.append(conditions)
        removed.append(lost)
    coupled.SUBDIVISION, coupled.DEGREE = subdivision, degree
    coupled.COMPRESSION = arb(compression)
    coupled.PROJECTION_BITS = projection_bits or bits
    coupled.SKIP_BUDGET = arb(tolerance)/(tn*rn*2)
    return dict(rule_setup_seconds=time.monotonic()-started,
                radial_rule='finite-window-gamma',
                radial_mass=str(sum(w for _, w in coupled.TS)),
                radial_centered_moment_checks=radial_audit['moment_checks'],
                owner_rule='conditional-band divided by owner share; explicit moment defects',
                owner_measure_audits=audits,
                physical_owner_masked_nodes=removed,
                warning='Discarded quadrature nodes have zero integrand under the unchanged '
                        'physical owner mask. This is not a bound on unobserved mass or on '
                        'the outer quadrature error.')


def owner_task(key):
    _, face, ir = key
    coupled.PS = OWNER_ROWS[face][ir]
    return ORIGINAL_TASK(key)


def sources():
    result = ORIGINAL_SOURCES()
    for name in [Path(__file__).name, 'riesz_owner_gauss.py', 'riesz_radial_gamma.py']:
        result[name] = hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
    return result


if __name__ == '__main__':
    coupled.prepare, coupled.task, coupled.sources = prepare, owner_task, sources
    coupled.main()
