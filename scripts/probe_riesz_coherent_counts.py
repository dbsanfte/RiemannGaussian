#!/usr/bin/env python3
"""Optional complete-count coherent-mode diagnostic, NOT a prime-sum bound.

On a fixed total-cofactor slice all legs on the same mode have one common
exponential, independent of count. Evaluate the remaining signed cutoff
response using the continuous renewal evaluator, including both empty atoms.
Balls pay its Taylor/propagation/projection errors. There is no outer
radial/factorial/owner integration, arithmetic transfer or Lean certificate.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path

from flint import acb, arb, ctx
from probe_riesz_continuous_balls import ContinuousCascade, real


def evaluate(bits, degree):
    ctx.prec = bits
    values = {}
    for multiplicity in [1, 3]:
        model = ContinuousCascade([acb(0)], [multiplicity], 51, subdivision=4, degree=degree)
        for p in [Q(21, 40), Q(11, 20), Q(14, 25)]:
            for lam in [Q(69, 100), Q(173285, 250000), Q(139, 200)]:
                faces = []
                for r, cap in [(Q(1, 100), 54), (Q(1, 25), 12)]:
                    s, d = (1-p)/r, (lam-p)/r
                    assert 0 < d < s
                    assert math.floor(s) <= cap  # No possible cofactor count is omitted.
                    value, audit = model.response(s, real(d))
                    assert value.is_finite() and value > 0
                    faces.append((value, str(audit['convolution_error']), math.floor(s)))
                joined = faces[0][0]-faces[1][0]
                assert joined < 0
                values[(multiplicity, p, lam)] = (faces, joined)
    return values


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    names = [Path(__file__).name, 'probe_riesz_continuous_balls.py']
    hashes = lambda: {n: hashlib.sha256(Path(__file__).with_name(n).read_bytes()).hexdigest() for n in names}
    frozen = hashes()
    first = evaluate(512, 96)
    fine = evaluate(768, 128)
    rows = []
    for key, (faces, joined) in fine.items():
        assert joined.overlaps(first[key][1])
        assert all(a[0].overlaps(b[0]) for a, b in zip(faces, first[key][0]))
        multiplicity, p, lam = key
        rows.append(dict(multiplicity=multiplicity, owner_share=str(p), cutoff_ratio=str(lam),
            lower_response=str(faces[0][0]), upper_response=str(faces[1][0]),
            lower_minus_upper=str(joined),
            maximum_possible_cofactor_counts=[f[2] for f in faces],
            projection_error_bounds=[f[1] for f in faces], refinements_overlap=True))
    u, delta, eta = arb(10001)/20000, arb(1)/40000, arb(3)/500
    p = arb(21)/40
    coherent = acb(u-delta, eta*(2*p-1))
    separate = acb(u-delta, eta)
    rate = (u/abs(coherent)).log()
    assert abs(separate) > u and abs(coherent) < u and rate > 0
    assert hashes() == frozen
    report = dict(scope=__doc__, source_sha256=frozen, rows=rows,
        literal_count_caps=[54, 12],
        common_head='The one-cofactor value m*d/s is independent of r and cancels '
                    'between these matched point profiles. This is not integration of the two factorial faces.',
        coupled_denominator=dict(source_radius=str(u), separate_mode_norm=str(abs(separate)),
            coherent_mode_norm=str(abs(coherent)), candidate_log_rate=str(rate),
            formula='w=(u-delta)+i*eta*(2*p-1), p=21/40',
            caveat='Rate of a constant-amplitude complete radial exponential moment only; '
                   'not an asymptotic, lower bound or divergence theorem for the full masked response.'),
        open='The full varying-amplitude radial/owner/factorial integral and actual prime sum are unestimated. '
             'Other modal assignments are not deleted on the basis of this fixed-slice diagnostic.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report['coupled_denominator'], indent=2))
    for row in rows:
        if row['owner_share'] == '21/40' and row['cutoff_ratio'] == '34657/50000':
            print(json.dumps(row, indent=2))


if __name__ == '__main__':
    main()
