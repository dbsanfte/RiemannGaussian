#!/usr/bin/env python3
"""Run the unchanged continuous coupled model with a gamma-weighted radial rule.

All CLI arguments, response calculations, two factorial beta faces, owner
weights, count allowances and row/error budgets come from the existing
driver. Only its prepared radial nodes/weights are replaced, BEFORE any
task is dispatched. The finite radial window and its mass remain exact.
The wrapper and new rule are included in every frozen source manifest.

This is still an optional numerical model, not an outer quadrature theorem
or an arithmetic estimate. A benchmark evaluates only two rows.
"""
import hashlib
from pathlib import Path

from flint import arb, ctx
import probe_riesz_joined_continuous_balls as coupled
from riesz_radial_gamma import gamma_rule


def main():
    original_prepare, original_sources = coupled.prepare, coupled.sources

    def prepare(n, tn, *args, **kwargs):
        audit = original_prepare(n, tn, *args, **kwargs)
        with ctx.workprec(max(4096, ctx.prec)):
            rule, checked = gamma_rule(n, arb(10001)/20000,
                                       arb(39)*n/20, arb(203)*n/100, tn)
        coupled.TS = rule
        audit.update(radial_rule='finite-window-gamma',
                     radial_mass=str(sum(w for _, w in rule)),
                     radial_centered_moment_checks=checked['moment_checks'])
        return audit

    def sources():
        answer = original_sources()
        for name in [Path(__file__).name, 'riesz_radial_gamma.py']:
            answer[name] = hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
        return answer

    coupled.prepare, coupled.sources = prepare, sources
    coupled.main()


if __name__ == '__main__':
    main()
