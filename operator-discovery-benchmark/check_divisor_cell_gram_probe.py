"""Independent direct-source replay of all declared cell Gram moments.

Uses only the standard library, with no producer or polynomial-library imports.
This checks the diagnostic, not feasibility of the enlarged certificate cone.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def read(p):
    return json.loads(p.read_text())


def digest(v):
    return hashlib.sha256(json.dumps(v, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def audit(directory):
    d = Path(directory).resolve()
    parent = ROOT / 'cancellation-arithmetic-results/divisor-cell-probe-001'
    inputs = {n: sha(d / n) for n in ['protocol.json', 'seal.json', 'results.json']}
    spec, seal, result = [read(d / n) for n in ['protocol.json', 'seal.json', 'results.json']]
    require(seal == dict(protocol_sha256=inputs['protocol.json'], code_sha256=spec['code_sha256']), 'protocol seal')
    for n, h in spec['code_sha256'].items():
        require(sha(ROOT / n) == h and sha(d / 'frozen_source' / n) == h, 'source hash ' + n)
    require(spec['parent_protocol_sha256'] == sha(parent / 'protocol.json'), 'parent protocol')
    dual_path = parent / 'jobs/dual-000.json'
    require(result['dual_input_sha256'] == sha(dual_path) and result['protocol_sha256'] == inputs['protocol.json'], 'result input hashes')
    dual = read(dual_path)['synthesis']
    require(dual['certified'] is True and dual['status'] == 'exact_separator', 'admitted original witness')
    expected = [dict(region=r, theta=t, power=j) for r in ['parent', 'child'] for t in ['1/3', '1/2', '2/3'] for j in [-1, 0, 1]]
    require(spec['contexts'] == expected and spec['scales'] == [1, 2, 3, 5], 'complete declared contexts')
    require(len(result['contexts']) == 18 and result['extension_chosen'] is False, 'complete results/no extension')
    require(len(dual['monomials']) == len(dual['weights']), 'moment dimensions')
    y = {(m['instance'], tuple(m['m'])): F(w) for m, w in zip(dual['monomials'], dual['weights'])}
    require(len(y) == len(dual['weights']), 'unique coordinates')
    checked, failures = [], 0
    for desc, observed in zip(expected, result['contexts']):
        require(all(observed[k] == v for k, v in desc.items()), 'context order')
        columns = [{}, {}, {}]
        theta = F(desc['theta'])
        for i, X in enumerate(spec['scales']):
            for t in range(X if desc['region'] == 'parent' else 2 * X,
                           2 * X if desc['region'] == 'parent' else 4 * X):
                # Exhaustive integer inequality, independent of binary root code.
                cut = max(k for k in range(t + 1) if k ** theta.denominator <= t ** theta.numerator)
                pref = {(a,): F(1) for a in range(1, t + 1)}
                contrast = {(): F(-1, 2)}
                # Divisor-first source order and explicit complementary sign.
                for divisor in range(1, t + 1):
                    sign = 1 if divisor <= cut else -1
                    for a in range(divisor, t + 1, divisor):
                        m = tuple(sorted((a, divisor)))
                        contrast[m] = contrast.get(m, F(0)) + F(sign, 2) * F(a) ** desc['power']
                for col, (left, right) in zip(columns, [(pref, pref), (pref, contrast), (contrast, contrast)]):
                    for lm, lq in left.items():
                        for rm, rq in right.items():
                            key = (i, tuple(sorted(lm + rm)))
                            col[key] = col.get(key, F(0)) + lq * rq
        serialized = [[dict(instance=i, m=list(m), coefficient=str(q)) for (i, m), q in sorted(col.items()) if q] for col in columns]
        require(digest(serialized) == observed['complete_column_sha256'], 'complete coefficient reconstruction')
        missing = sorted({key for col in columns for key, q in col.items() if q and key not in y})
        require(not missing and observed['unsupported_coordinates'] == [] and observed['status'] == 'supported', 'complete moment domain')
        a, b, c = [sum((q * y[key] for key, q in col.items() if q), F(0)) for col in columns]
        determinant = a * c - b * b
        psd = a >= 0 and c >= 0 and determinant >= 0
        require([observed[k] for k in ['a', 'b', 'c', 'determinant']] == list(map(str, [a, b, c, determinant])), 'exact moments')
        require(observed['PSD'] is psd and observed['old_witness_separates_this_2x2_cone'] is psd, 'PSD status')
        failures += not psd
        checked.append(dict(desc, moments=list(map(str, [a, b, c])), determinant=str(determinant), PSD=psd))
    require(result['full_2x2_failures'] == failures and result['unknown_contexts'] == 0, 'summary')
    require(all(result[k] is False for k in ['global_bound_proved', 'RH_proved']), 'no global promotion')
    example = next(r for r in checked if r['region'] == 'child' and r['theta'] == '2/3' and r['power'] == 1)
    a, b, c = map(F, example['moments'])
    direction_dot = a - 4 * b + 4 * c
    require(direction_dot == -1, 'exact separating direction')
    require(inputs == {n: sha(d / n) for n in inputs}, 'end input binding')
    return dict(all_passed=True, input_sha256=inputs, dual_sha256=sha(dual_path),
                verifier_sha256=sha(Path(__file__)), contexts_verified=18,
                full_2x2_failures=failures, unsupported_coordinates=0,
                simple_direction=dict(context=example, square='(P-2D)^2', old_dual_dot=str(direction_dot)),
                scope='independent diagnostic replay; original witness invalid for larger Gram cone; no feasibility theorem',
                global_bound_proved=False, RH_proved=False)


if __name__ == '__main__':
    directory = Path(sys.argv[1])
    verified = audit(directory)
    with (directory / 'independent_verification.json').open('x') as f:
        json.dump(verified, f, sort_keys=True, indent=2)
        f.write('\n')
    print(json.dumps({k: v for k, v in verified.items() if k not in ['input_sha256', 'simple_direction']}))
