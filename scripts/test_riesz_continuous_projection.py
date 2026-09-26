#!/usr/bin/env python3
"""Optional independent regressions for the interval-parameter projection.

Keep outside ordinary CI and certificate verification. These checks validate
the numerical model evaluator, not the arithmetic transfer or outer integral.
"""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, arb, ctx
from probe_riesz_continuous_balls import ContinuousCascade, elementary_checks, real
from riesz_continuous_projection import compress_model, count_allowance, response_interval


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    ctx.prec = 768
    names = ['test_riesz_continuous_projection.py', 'riesz_continuous_projection.py',
             'probe_riesz_continuous_balls.py']
    hashes = lambda: {p: hashlib.sha256(Path(__file__).with_name(p).read_bytes()).hexdigest()
                      for p in names}
    frozen = hashes()
    nodes = [acb(-arb(1)/7), acb(0, arb(1)/3), acb(0, -arb(1)/3)]
    base = ContinuousCascade(nodes, [1, 3, 3], 4, 8, 96)
    compressed = ContinuousCascade(nodes, [1, 3, 3], 4, 8, 96)
    compress_model(compressed, arb('1e-35'))
    rows = []
    for s in [Fraction(5, 2), Fraction(99, 37), Fraction(3)]:
        d = arb(7)/5
        original, _ = base.response(s, d)
        projected = response_interval(base, real(s), d)
        fast = response_interval(compressed, real(s), d)
        envelope = response_interval(compressed, real(s), d, negligible=lambda bound: True)
        assert original.overlaps(projected) and original.overlaps(fast)
        assert abs(original) < abs(envelope).upper()
        assert abs(original) < count_allowance(real(s), d)
        assert projected.rad() < arb('1e-45') and fast.rad() < arb('1e-30')
        rows.append(dict(s=str(s), d='7/5', original=str(original),
                         interval_projection=str(projected), compressed=str(fast),
                         norm_envelope=str(envelope), overlap=True))
    s = real(Fraction(99, 37))+arb(0, '1e-55')
    v = response_interval(compressed, s, arb(7)/5)
    assert v.overlaps(arb(rows[1]['original'])) and v.rad() < arb('1e-30')
    rows.append(dict(interval_parameter=str(s), value=str(v), overlap=True))
    # Reference includes a separate count-by-count subset integral, not the
    # interval convolution or its compression/error-envelope implementation.
    independent = elementary_checks()
    assert hashes() == frozen
    result = dict(scope='Optional numerical regression only; no arithmetic or outer '
                        'quadrature estimate.', cases=rows,
                  independent_elementary_checks=independent, source_sha256=frozen)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print('Four projection/compression/envelope checks and nine elementary checks passed.')


if __name__ == '__main__':
    main()
