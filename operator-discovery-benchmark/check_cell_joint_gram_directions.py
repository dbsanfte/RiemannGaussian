"""Direct-source verification of the two joint-channel obstruction witnesses."""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())


def verify(directory):
    d = Path(directory).resolve()
    parent = ROOT / 'cancellation-arithmetic-results/cell-shared-gram-native-replay-001'
    original = read(parent / 'result.json')
    admission = read(parent / 'independent_verification.json')
    if admission.get('all_passed') is not True:
        raise ValueError('original exact cone admission required')
    dual = original['synthesis']
    y = {(r['instance'], tuple(r['m'])): F(q) for r, q in zip(dual['monomials'], dual['weights'])}
    proposed = read(d / 'simple_directions.json')
    if proposed['source_results_sha256'] != sha(d / 'results.json'):
        raise ValueError('joint result binding')
    result = read(d / 'results.json')
    for name, h in result['input_sha256'].items():
        if sha(ROOT / name) != h:
            raise ValueError('joint input binding')
    reports = {}
    for region, sign in [('parent', 1), ('child', -1)]:
        observed = proposed['directions'][region]
        if observed['indices'] != [1, 2] or observed['coefficients'] != [1, sign]:
            raise ValueError('declared two-channel direction')
        column = {}
        for k, X in enumerate(original['scales']):
            ts = range(X, 2 * X) if region == 'parent' else range(2 * X, 4 * X)
            for t in ts:
                cut = max(n for n in range(t + 1) if n ** 3 <= t)
                # D_-1 + sign*D_0 combines weights 1/a + sign;
                # its complete formal constant is -(1+sign)/2.
                q = {(): -F(1 + sign, 2)} if 1 + sign else {}
                for divisor in range(1, t + 1):
                    cell_sign = 1 if divisor <= cut else -1
                    for a in range(divisor, t + 1, divisor):
                        mon = tuple(sorted((a, divisor)))
                        coefficient = F(cell_sign, 2) * (F(1, a) + sign)
                        q[mon] = q.get(mon, F(0)) + coefficient
                q = {m: c for m, c in q.items() if c}
                for lm, lc in q.items():
                    for rm, rc in q.items():
                        key = (k, tuple(sorted(lm + rm)))
                        column[key] = column.get(key, F(0)) + lc * rc
        column = {m: c for m, c in column.items() if c}
        if any(key not in y for key in column):
            raise ValueError('missing moment; no zero extension allowed')
        value = sum((q * y[m] for m, q in column.items()), F(0))
        if value >= 0 or str(value) != observed['quadratic_value']:
            raise ValueError('complete exact negative square pairing')
        reports[region] = dict(complete_source_verified=True, column_monomials=len(column),
                                exact_negative_pairing=str(value), coefficients=[1, sign])
    return dict(all_passed=True, input_sha256={n: sha(d / n) for n in ['results.json', 'simple_directions.json', 'independent_verification.json']},
                original_dual_sha256=sha(parent / 'result.json'), verifier_sha256=sha(Path(__file__)),
                directions=reports, scope='two complete symbolic square columns independently reconstructed; original witness invalid for joint cone; no feasibility claim',
                global_bound_proved=False, RH_proved=False)


if __name__ == '__main__':
    d = Path(sys.argv[1]); report = verify(d)
    with (d / 'root_direction_verification.json').open('x') as f:
        json.dump(report, f, sort_keys=True, indent=2); f.write('\n')
    print(json.dumps(dict(all_passed=report['all_passed'], regions=list(report['directions']), global_bound_proved=False, RH_proved=False)))
