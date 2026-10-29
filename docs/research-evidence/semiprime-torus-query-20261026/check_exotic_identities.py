#!/usr/bin/env python3
"""Exact finite-field checks of identities, not a factoring benchmark."""
import json
from pathlib import Path

P = 1009


def det(a):
    a = [[x % P for x in row] for row in a]
    out = 1
    for k in range(len(a)):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            out = -out
        v = a[k][k]
        out = out * v % P
        inv = pow(v, -1, P)
        for i in range(k + 1, len(a)):
            scale = a[i][k] * inv % P
            for j in range(k, len(a)):
                a[i][j] = (a[i][j] - scale * a[k][j]) % P
    return out % P


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = (out[i + j] + x * y) % P
    return out


def product(xs):
    out = 1
    for x in xs:
        out = out * x % P
    return out


def polynomial(roots):
    out = [1]
    for x in roots:
        out = mul(out, [1, -x])
    return out


def series(numer, denom, n):
    assert denom[0] == 1
    out = []
    for k in range(n):
        out.append(((numer[k] if k < len(numer) else 0)
                    - sum(denom[i] * out[k-i]
                          for i in range(1, min(k, len(denom)-1)+1))) % P)
    return out


def remainder(numer, denom):
    a = numer[:]
    inv = pow(denom[-1], -1, P)
    for k in range(len(a)-len(denom), -1, -1):
        c = a[k+len(denom)-1] * inv % P
        for i, x in enumerate(denom):
            a[k+i] = (a[k+i] - c*x) % P
    return a[:len(denom)-1]


def one_case(ts, rho, h):
    jn = len(ts)
    us = [pow(rho, i, P) for i in range(h)]
    value = product(1-t*u for t in ts for u in us)
    xs = [pow(t, -1, P) for t in ts]
    g, dx = polynomial(us), polynomial(xs)
    hs = series(g, dx, h+jn)
    jt = [[hs[h-r+s] for s in range(jn)] for r in range(jn)]
    assert det(jt) == value * product(pow(t, -h, P) for t in ts) % P
    # One global rank-one source, using the finite barycentric identity.
    f = product(1-pow(rho, k, P) for k in range(1, h))
    ci = []
    for i in range(h):
        at_root = product(1-pow(rho, k-i, P) for k in range(h) if k != i)
        ci.append(f*pow(at_root, -1, P) % P)
    row_values = [product(1-t*u for u in us) for t in ts]
    masses = [(1-t*u) % P for t in ts for u in us]
    for marked in (False, True):
        marks = [j*j+2 for j in range(jn)] if marked else [1]*jn
        source = [marks[j]*ci[i]*pow(f, -1, P) % P
                  for j in range(jn) for i in range(h)]
        reset = [[int(i == j)*masses[i]+source[j] for j in range(jn*h)]
                 for i in range(jn*h)]
        jet = sum(marks[j]*product(a for k, a in enumerate(row_values) if k != j)
                  for j in range(jn)) % P
        assert det(reset) == (value+jet) % P
    if h >= jn:
        rem = remainder(g, dx)
        rs = series(rem, dx, h+jn)
        assert rs[h-jn+1:] == hs[h-jn+1:]

    # Arcs indexed as all row->clock, then all clock->row.
    arcs = [(j, jn+i, ts[j]) for j in range(jn) for i in range(h)]
    arcs += [(jn+i, j, us[i]) for j in range(jn) for i in range(h)]
    nb = [[int(e == f) - (weight if head == tail2 and head2 != tail else 0)
           for f, (tail2, head2, weight) in enumerate(arcs)]
          for e, (tail, head, _) in enumerate(arcs)]
    edge_det = det(nb)
    aj = [[(int(j != k)*ts[k]) % P for k in range(jn)] for j in range(jn)]
    ah = [[(us[i]*int(i != l)) % P for l in range(h)] for i in range(h)]
    tensor = [[int(j == k and i == l)-aj[j][k]*ah[i][l]
               for k in range(jn) for l in range(h)]
              for j in range(jn) for i in range(h)]
    assert det(tensor) == edge_det
    if value:
        vertex = [[int(i == j) for j in range(jn+h)] for i in range(jn+h)]
        for j, t in enumerate(ts):
            for i, u in enumerate(us):
                inv = pow((1-t*u) % P, -1, P)
                vertex[j][j] += t*u*inv
                vertex[jn+i][jn+i] += t*u*inv
                vertex[j][jn+i] -= t*inv
                vertex[jn+i][j] -= u*inv
        assert edge_det == value*det(vertex) % P
    # Euler transform of characteristic polynomial, at several public scalars.
    for z in (0, 1, 7, 73):
        fp = product(z+t for t in ts)
        derivative = sum(product(z+t for k, t in enumerate(ts) if k != omit)
                         for omit in range(jn)) % P
        matrix = [[int(j == k)*z-aj[j][k] for k in range(jn)] for j in range(jn)]
        assert det(matrix) == (z*derivative-(jn-1)*fp) % P
    return {'J': jn, 'h': h, 'T': ts, 'rho': rho,
            'native_product': value, 'nonbacktracking_determinant': edge_det,
            'native_collision': value == 0, 'passed': True}


def lucas_checks():
    w = pow(11, 16, P)
    denom = (w-pow(w, -1, P)) % P
    def lucas(m):
        return (pow(w, m, P)-pow(w, -m, P))*pow(denom, -1, P) % P
    k, h = 2, 7
    c = (pow(w, k, P)+pow(w, -k, P)) % P
    invariant = lucas(k)**2 % P
    assert invariant and c != 2
    count = 0
    for d in (2, 4, 6, 8, 10, 12, 19):
        ss = [lucas(d-k*i) for i in range(h+2)]
        assert ss[0] and ss[h]
        for i in range(h):
            assert (ss[i]*ss[i+2]-ss[i+1]**2+invariant) % P == 0
        endpoint = (ss[1]*pow(ss[0], -1, P)-ss[h+1]*pow(ss[h], -1, P)) % P
        finite_part = 0
        for a, b in zip(ss[:h], ss[1:h+1]):
            assert a or b
            finite_part += pow(a*b, -1, P) if a and b else -pow(a or b, -2, P)
        flag = sum(x == 0 for x in ss[:h])
        assert (invariant*finite_part-endpoint)*pow(c-2, -1, P) % P == flag
        for delta in range(1, 17):
            aa = [(x+delta) % P for x in ss]
            if not all(aa):
                continue
            adj_sum = sum(pow(aa[i]*aa[i+1], -1, P) for i in range(h))
            single_sum = sum(pow(aa[i], -1, P) for i in range(h))
            ep = aa[1]*pow(aa[0], -1, P)-aa[h+1]*pow(aa[h], -1, P)
            assert ((invariant+delta*delta*(c-2))*adj_sum-ep
                    -delta*(c-2)*single_sum) % P == 0
            count += 1
    return {'rows': 7, 'regular_parameter_checks': count,
            'finite_part_flags_checked': 7, 'all_passed': True}


def main():
    cases = []
    for jn, h in ((1, 2), (2, 2), (2, 3), (3, 2), (3, 4)):
        for rho in (7, 11):
            for ts in (list(range(2, jn+2)), [2]*jn,
                       [1]+list(range(2, jn+1))):
                cases.append(one_case(ts, rho, h))
    missed = [c for c in cases if c['native_collision'] and c['nonbacktracking_determinant']]
    assert missed, 'Demonstrate that the graph determinant alone loses collision support.'
    report = {'modulus': P, 'scope': 'exact algebra identities, no native coverage/exponent claim',
              'case_count': len(cases), 'all_passed': True,
              'rank_one_source_checks': 2*len(cases),
              'lucas': lucas_checks(),
              'graph_determinant_misses_native_zero_count': len(missed),
              'cases': cases}
    Path(__file__).with_name('exotic-checks.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'cases'}))


if __name__ == '__main__':
    main()
