#!/usr/bin/env python3
"""Optional numerical diagnostic for literal factorial allocation variation.

This probes binomial weights, not a prime or source-scale certificate.
The rigorous bound is in ZetaRieszAllocationVariation. No CI invokes this.
"""
from pathlib import Path
import hashlib
import json
import math
import numpy as np
from scipy.stats import binom


def run():
    rows = []
    for n in [256, 640, 1536, 4096, 8192, 65536, 1_000_000]:
        v = 2*n
        delta = math.pi/54
        b = .406125*v
        small = math.log(2)
        # Four fixed cofactor-prime logs, plus the literal small-prime log.
        fixed_logs = (b-small)*np.array([.247, .249, .251, .253])
        ts = np.linspace(v-delta, v+delta, 4097)
        # The small prime is ineligible; fixed large cofactor incidences remain.
        xs = np.vstack([b/ts, *(1-logq/ts for logq in fixed_logs)])
        low, high = n//5+2, 13*n//32
        mass = binom.cdf(high, n+1, xs)-binom.cdf(low-1, n+1, xs)
        theta = mass.sum(axis=0)
        actual_span = float(theta.max()-theta.min())
        proved_span = 3*math.sqrt(n+1)/v
        rows.append(dict(N=n, owner_share_at_center=1-b/v,
                         allocated_at_center=float(theta[len(ts)//2]),
                         unallocated_at_center=float(1-theta[len(ts)//2]),
                         allocation_span=actual_span,
                         rigorous_six_incidence_span_bound=proved_span,
                         sampled_ratio=actual_span/proved_span))
    return dict(model_only=True,
                scope='Binomial allocation diagnostic; no literal prime-sum or source-scale certificate',
                owner_transition=19/32,
                full_period_width=2*math.pi/54,
                cofactor_share=.406125,
                rows=rows,
                source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == '__main__':
    payload = run()
    Path('docs/riesz-allocation-transition-probe.json').write_text(json.dumps(payload, indent=2)+'\n')
    print(json.dumps(payload, indent=2))
