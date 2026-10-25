#!/usr/bin/env python3
"""Exact public-input Cayley companion; controls are not coverage/rate claims."""
import argparse
import json
import math
from pathlib import Path
import runpy


def locate_repo(explicit=None):
    candidates = ([Path(explicit)] if explicit else []) + list(Path(__file__).resolve().parents)
    for root in candidates:
        if (root / 'scripts/probe_semiprime_long_period.py').is_file():
            return root
    raise FileNotFoundError('Supply --repo-root containing scripts/probe_semiprime_long_period.py')


def load_batch(root):
    return runpy.run_path(str(root / 'scripts/probe_semiprime_long_period.py'))['MonicBatch']


def companion(N, targets, u, q, L, Batch, *, odd_subgroup_promised):
    """No factors as inputs. Promise: all inputs belong to one odd-order subgroup.

    Unit checks certify all denominators actually used, not the subgroup promise.
    Core constructs block/remainder seeds, but no full length-L seed list.
    """
    if not odd_subgroup_promised:
        raise ValueError('Prepared odd-subgroup promise required')
    if N < 3 or N % 2 == 0 or L < 0:
        raise ValueError('Require odd N>=3 and L>=0')
    targets = [int(x) % N for x in targets]
    u, q = int(u) % N, int(q) % N
    def unit(x, label):
        if math.gcd(x, N) != 1:
            raise ValueError('Nonunit ' + label)
        return pow(x, -1, N)
    unit(u, 'u'); unit(q, 'q')
    unit(u+1, 'u+1'); qi = unit(q+1, 'q+1')
    transformed, A = [], 1
    for x in targets:
        unit(x, 'target')
        xi = unit(x+1, 'target+1')
        transformed.append((x-1)*xi % N)
        A = A*(x+1) % N
    class CountedBatch(Batch):
        def __init__(self, n):
            super().__init__(n)
            self.max_convolution_degree = 0
        def mul(self, a, b):
            if a and b:
                self.max_convolution_degree = max(self.max_convolution_degree, len(a)+len(b)-2)
            return super().mul(a, b)
    batch = CountedBatch(N)
    b = math.isqrt(L) or 1
    K, r = divmod(L, b)
    # Balanced construction of f(X)=prod_(h<b)(1+u*q^h*X).
    coefficients, t = [], u
    if K:
        for _ in range(b):
            coefficients.append([1, t])
            t = t*q % N
        while len(coefficients) > 1:
            coefficients = [batch.mul(coefficients[i], coefficients[i+1])
                            if i+1 < len(coefficients) else coefficients[i]
                            for i in range(0, len(coefficients), 2)]
        f = coefficients[0]
        points, t, stride = [], 1, pow(q, b, N)
        for _ in range(K):
            points.append(t)
            t = t*stride % N
        values = batch.evaluate(f, points)
    else:
        f, points, values = [1], [], []
    B = 1
    for value in values:
        B = B*value % N
    t = u*pow(q, K*b, N) % N
    for _ in range(r):
        B = B*(1+t) % N
        t = t*q % N
    Bi = unit(B, 'seed plus norm B')
    Ai = unit(A, 'target plus norm A')
    J = len(targets)
    C = pow(2, J*L, N)*pow(Ai, L, N)*pow(Bi, J, N) % N
    v = (q-1)*qi % N
    unit(1-v*v, 'Mobius determinant')
    return {'N': N, 'J': J, 'L': L, 'A': A, 'B': B, 'C': C,
            'transformed_targets': transformed,
            'mobius': {'v': v, 'matrix': [[1, v], [v, 1]], 'initial': (u-1)*pow(u+1, -1, N)%N},
            'counts': dict(batch.stats(), block_length=b, full_blocks=K,
                           remainder_factors=r, factor_degree=len(f)-1,
                           point_tree_degree=K,
                           max_convolution_degree=batch.max_convolution_degree,
                           full_seed_list_materialized=False,
                           seed_generator_steps=(b if K else 0)+K+r),
            'domain': 'odd-subgroup promise supplied; all used denominator norms checked'}


def controls(Batch):
    N, gamma = 77, 4  # Orders 3 and 5; factors are test-oracle metadata only.
    residues = [pow(gamma, i, N) for i in range(15)]
    cases, masks, aggregate_masks, max_degree, max_tree, max_conv = 0, set(), set(), 0, 0, 0
    for L in [0, 1, 2, 7, 16, 23, 65, 1024]:
        for exponents in [[], [0], [1, 3, 5, 9], list(range(15))]:
            for q in [1, gamma, pow(gamma, 3, N)]:
                u = pow(gamma, 2, N)
                xs = [residues[e] for e in exponents]
                out = companion(N, xs, u, q, L, Batch, odd_subgroup_promised=True)
                ys = [u*pow(q, i, N)%N for i in range(L)]  # Oracle only.
                T = lambda t: (t-1)*pow(t+1, -1, N)%N
                R, RT, literal_B = 1, 1, 1
                for y in ys:
                    literal_B = literal_B*(y+1)%N
                assert literal_B == out['B']
                for x in xs:
                    for y in ys:
                        g, gt = math.gcd(x-y, N), math.gcd(T(x)-T(y), N)
                        assert g == gt
                        masks.add(g)
                        R = R*(x-y)%N
                        RT = RT*(T(x)-T(y))%N
                assert out['C']*R%N == RT
                aggregate_masks.add(math.gcd(R, N))
                assert out['transformed_targets'] == [T(x) for x in xs]
                v = out['mobius']['v']
                for y in ys:
                    s = T(y)
                    assert math.gcd(1+v*s, N) == 1
                    assert (s+v)*pow(1+v*s, -1, N)%N == T(q*y%N)
                c = out['counts']
                assert c['remainder_factors'] < c['block_length']
                assert c['full_seed_list_materialized'] is False
                max_degree = max(max_degree, c['factor_degree'])
                max_tree = max(max_tree, c['point_tree_degree'])
                max_conv = max(max_conv, c['max_convolution_degree'])
                cases += 1
    assert masks == {1, 7, 11, 77}
    assert aggregate_masks == {1, 7, 11, 77}
    rejections = 0
    for kwargs in [dict(u=-1), dict(q=-1), dict(targets=[-1]),
                   dict(odd_subgroup_promised=False), dict(u=1, q=2, L=6)]:
        args = dict(N=N, targets=[1], u=gamma, q=gamma, L=7,
                    Batch=Batch, odd_subgroup_promised=True)
        args.update(kwargs)
        try:
            companion(**args)
        except ValueError:
            rejections += 1
        else:
            raise AssertionError('Missing domain rejection')
    assert rejections == 5
    return {'status': 'passed', 'cases': cases, 'leaf_gcd_masks': sorted(masks),
            'aggregate_gcd_masks': sorted(aggregate_masks),
            'domain_rejections': rejections, 'max_factor_degree': max_degree,
            'max_point_tree_degree': max_tree, 'max_convolution_degree': max_conv,
            'scope': 'exact conventions/composite arithmetic; no coverage, timing or rate claim'}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root')
    p.add_argument('--test', action='store_true')
    p.add_argument('--json-out', type=Path)
    p.add_argument('--N', type=int)
    p.add_argument('--targets', default='', help='comma-separated residues')
    p.add_argument('--u', type=int)
    p.add_argument('--q', type=int)
    p.add_argument('--L', type=int)
    p.add_argument('--odd-subgroup-promised', action='store_true')
    a = p.parse_args()
    Batch = load_batch(locate_repo(a.repo_root))
    if a.test:
        result = controls(Batch)
    else:
        if any(v is None for v in [a.N, a.u, a.q, a.L]):
            p.error('Supply --test or --N --u --q --L')
        result = companion(a.N, [int(t) for t in a.targets.split(',') if t],
                           a.u, a.q, a.L, Batch,
                           odd_subgroup_promised=a.odd_subgroup_promised)
    rendered = json.dumps(result, indent=2, sort_keys=True)+'\n'
    if a.json_out:
        a.json_out.write_text(rendered)
    print(rendered, end='')

if __name__ == '__main__':
    main()
