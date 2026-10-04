#!/usr/bin/env python3
"""Optional proven-prime cache for the five joined-pair discovery tests.

Incremental, reproducible rejection sampling. FLINT proves each accepted
prime; the cache is not a Lean certificate or a prime-population estimate.
This file stays separate from analysis so a running sample job is frozen.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
from flint import ctx
from probe_riesz_balanced_prime_sampling import sample_primes
from probe_riesz_pair_structure import SHARES


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def plan():
    rows = []
    for seed in (731, 732):
        for i, share in enumerate(SHARES):
            q = round(1280*share)
            rows.append(dict(id=f'640-share-{i}-{seed}', N=640, seed=seed,
                kind='bulk', share=share, pLogLower=1280-q, qLogLower=q, size=8))
        rows.append(dict(id=f'1536-balanced-{seed}', N=1536, seed=seed,
            kind='native_order', share=.495, pLogLower=1551, qLogLower=1521, size=8))
        for name, p, q in (
            ('prefix_transition', 305, 207),
            ('owner_lower', 261, 251),
            ('owner_upper_left', 319, 193),
            ('owner_upper_right', 320, 192),
            ('radial_lower', 263, 241),
            ('radial_upper', 276, 242)):
            rows.append(dict(id=f'256-{name}-{seed}', N=256, seed=seed,
                kind=name, pLogLower=p, qLogLower=q, size=16))
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path,
                    default=Path('.lake/riesz-pair-joint/new-primes.json'))
    args = ap.parse_args()
    specs = plan()
    frozen = dict(generator=digest(__file__),
        sampler=digest('scripts/probe_riesz_balanced_prime_sampling.py'),
        shares=digest('scripts/probe_riesz_pair_structure.py'))
    if args.output.exists():
        cache = json.loads(args.output.read_text())
        assert cache['plan'] == specs and cache['sourceSha256'] == frozen
    else:
        cache = dict(classification='Incremental proven-prime sampling for joined discovery; no floor credit',
            plan=specs, sourceSha256=frozen, rows=[], complete=False,
            samplingWithReplacement=True, primeProofMethod='FLINT is_prime after GMP probable-prime filter',
            provedInLean=False, independentCofinalBound=False)
    assert len({r['id'] for r in cache['rows']}) == len(cache['rows'])
    existing = {r['id'] for r in cache['rows']}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    start = time.monotonic()
    for i, spec in enumerate(specs):
        if spec['id'] in existing:
            continue
        N = spec['N']
        ctx.prec = max(1200, math.ceil(2*N/math.log(2))+256)
        assert spec['qLogLower'] > 16*math.log(N)
        assert spec['pLogLower'] > spec['qLogLower']+1
        print(json.dumps(dict(stage='sampling', row=spec['id'], sizePerLeg=spec['size'])), flush=True)
        left = sample_primes(spec['pLogLower'], spec['size'], 92117+10000*N+100*i+spec['seed'])
        right = sample_primes(spec['qLogLower'], spec['size'], 93419+10000*N+100*i+spec['seed'])
        assert min(map(int, left['primes'])) > max(map(int, right['primes'])) > N**16
        cache['rows'].append(dict(**spec, left=left, right=right))
        temporary = args.output.with_suffix('.tmp')
        temporary.write_text(json.dumps(cache, indent=2)+'\n')
        temporary.replace(args.output)
        print(json.dumps(dict(stage='cached', row=spec['id'], rows=len(cache['rows']),
                              elapsedSeconds=time.monotonic()-start)), flush=True)
    cache['complete'] = len(cache['rows']) == len(specs)
    assert cache['complete'] and {r['id'] for r in cache['rows']} == {r['id'] for r in specs}
    assert frozen == dict(generator=digest(__file__),
        sampler=digest('scripts/probe_riesz_balanced_prime_sampling.py'),
        shares=digest('scripts/probe_riesz_pair_structure.py'))
    args.output.write_text(json.dumps(cache, indent=2)+'\n')
    print(json.dumps(dict(output=str(args.output), complete=True, rows=len(specs), floor=False)))


if __name__ == '__main__':
    main()
