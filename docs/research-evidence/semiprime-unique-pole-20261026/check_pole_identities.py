#!/usr/bin/env python3
"""Exact finite-field diagnostics of paper identities, not a factoring benchmark."""
import argparse
import json
from pathlib import Path
P = 101

def trim(a):
    a = [x % P for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def add(a, b):
    return trim([(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])

def scale(a, c):
    return trim([c*x for x in a])

def mul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)

def divmod_poly(a, b):
    a, b = trim(a), trim(b)
    assert b != [0]
    out = [0]*max(1, len(a)-len(b)+1)
    while a != [0] and len(a) >= len(b):
        k = len(a)-len(b)
        c = a[-1]*pow(b[-1], -1, P) % P
        out[k] = c
        a = add(a, scale([0]*k+b, -c))
    return trim(out), a

def rem(a, b):
    return divmod_poly(a, b)[1]

def val(a, x):
    out = 0
    for c in reversed(a):
        out = (out*x+c) % P
    return out

def prod(polys):
    out = [1]
    for a in polys:
        out = mul(out, a)
    return out

def deriv(a):
    return trim([i*a[i] for i in range(1, len(a))] or [0])

def coeff(a, i):
    return a[i] if i < len(a) else 0

def det(matrix):
    if not matrix:
        return 1
    a = [row[:] for row in matrix]
    out = 1
    for i in range(len(a)):
        pivot = next((j for j in range(i, len(a)) if a[j][i] % P), None)
        if pivot is None:
            return 0
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            out = -out
        out = out*a[i][i] % P
        inv = pow(a[i][i], -1, P)
        for j in range(i+1, len(a)):
            c = a[j][i]*inv % P
            a[j] = [(x-c*y) % P for x, y in zip(a[j], a[i])]
    return out % P

def multiplication_matrix(poly, modulus):
    n = len(modulus)-1
    columns = [rem([0]*i+poly, modulus) for i in range(n)]
    return [[coeff(columns[j], i) for j in range(n)] for i in range(n)]

def adjugate_column_zero(matrix):
    n = len(matrix)
    return trim([(-1)**i*det([[matrix[r][c] for c in range(n) if c != i]
                             for r in range(1, n)]) for i in range(n)])

def interpolate(xs, ys):
    out = [0]
    for i, x in enumerate(xs):
        basis = prod([[-y, 1] for j, y in enumerate(xs) if i != j])
        out = add(out, scale(basis, ys[i]*pow(val(basis, x), -1, P)))
    return out

def inverse_mod(a, modulus):
    r0, r1 = modulus, rem(a, modulus)
    s0, s1 = [0], [1]
    while r1 != [0]:
        quotient, r2 = divmod_poly(r0, r1)
        r0, r1 = r1, r2
        s0, s1 = s1, add(s0, scale(mul(quotient, s1), -1))
    assert len(r0) == 1 and r0[0]
    return rem(scale(s0, pow(r0[0], -1, P)), modulus)

def run():
    checks = {}
    q, h = 2, 6
    rho = pow(q, -1, P)
    clocks = [pow(q, i, P) for i in range(h)]
    xnodes = [pow(rho, i, P) for i in range(h)]
    W = prod([[-x, 1] for x in xnodes])
    kappa = 1
    for i in range(1, h):
        kappa = kappa*(1-pow(rho, i, P)) % P
    ci = [kappa*pow(x, h-1, P)*pow(val(deriv(W), x), -1, P) % P for x in xnodes]
    def lam(values):
        return sum(c*v for c, v in zip(ci, values)) % P
    def check(name, truth):
        assert truth, name
        checks[name] = checks.get(name, 0)+1
    for roots in ([4, 13], [8, 13, 17], [4, 13, 17, 19],
                  [4, 13, 13, 17], [13, 17, 19], [2, 4, 13]):
        D = prod([[-x, 1] for x in roots])
        J = len(roots)
        v, Wt = [1], [1]
        eta = []
        for t in range(h+1):
            check('adjugate_column_recurrence', v == adjugate_column_zero(multiplication_matrix(Wt, D)))
            if t == h:
                break
            a = clocks[t]
            eta.append(val(v, a))
            Qa, residual = divmod_poly(add(D, [-val(D, a)]), [-a, 1])
            check('synthetic_division', residual == [0])
            r = rem(mul(Qa, v), D)
            check('top_coefficient_update', coeff(r, J-1) == val(v, a))
            check('second_coefficient_update', coeff(r, J-2) == ((a+D[J-1])*val(v, a)-val(D, a)*coeff(v, J-1)) % P)
            v = scale(r, (-1)**(J+1))
            Wt = mul(Wt, [-a, 1])
        # Independently evaluate the divided-difference scalar recurrence.
        en = [1]
        for n in range(1, h):
            total = 0
            for k in range(1, min(J, n)+1):
                nodes = clocks[n-k:n+1]
                dd = [val(D, x) for x in nodes]
                for order in range(1, k+1):
                    dd = [(dd[j+1]-dd[j])*pow((nodes[j+order]-nodes[j]) % P, -1, P) % P
                          for j in range(len(dd)-1)]
                product = 1
                for i in range(n-k+1, n):
                    product = product*val(D, clocks[i]) % P
                total += dd[0]*product*en[n-k]
            en.append(-total % P)
        for n in range(h):
            check('scalar_newton_recurrence', en[n] == (-1)**(J*n)*eta[n] % P)
        hits = [x for x in roots if x in clocks]
        if len(hits) == 1:
            A = coeff(v, J-1)
            B = (D[J-1]*A-coeff(v, J-2)) % P
            check('unique_hit_locator', A != 0 and -B*pow(A, -1, P) % P == hits[0])
            scalar_theta = (clocks[-1]+val(D, clocks[-1])*en[-2]*pow(en[-1], -1, P)) % P
            check('two_final_scalars_locator', scalar_theta == hits[0])
    roots, tags = [4, 13, 17, 19], [7, 11, 5, 9]
    J = len(roots)
    D = prod([[-x, 1] for x in roots])
    alpha = [pow(x, J-1, P)*pow(val(deriv(D), x), -1, P) % P for x in roots]
    Q = interpolate(roots, [u*pow(x, J-1, P) % P for x, u in zip(roots, tags)])
    Qrev = [coeff(Q, J-1-i) for i in range(J)]
    for A in (1, 3, 5, 7, 9):
        factors = [[A, -x] for x in roots]
        DA = prod(factors)
        numerator, tagged = [0], [0]
        for j in range(J):
            cofactor = prod(factors[:j]+factors[j+1:])
            numerator = add(numerator, scale(cofactor, alpha[j]))
            tagged = add(tagged, scale(cofactor, alpha[j]*tags[j]))
        target = trim([coeff(Q, J-1-i)*pow(A, J-1-i, P) for i in range(J)])
        check('constant_numerator_identity', numerator == [pow(A, J-1, P)])
        check('tagged_numerator_identity', tagged == target)
        values = [val(DA, x) for x in xnodes]
        if all(values):
            actual = lam([pow(y, -1, P) for y in values])
            inverse = inverse_mod(DA, W)
            selected = kappa*coeff(rem(mul([0]*(h-1)+[1], inverse), W), h-1) % P
            check('finite_selected_inverse', actual == selected)
            rhs = 0
            for x, weight in zip(roots, alpha):
                Gh = 1
                for node in xnodes:
                    Gh = Gh*(1-x*pow(A, -1, P)*node) % P
                rhs += weight*pow(Gh, -1, P)
            rhs = kappa*pow(A, -J, P)*rhs % P
            check('finite_reciprocity', actual == rhs)
    hit_i = clocks.index(roots[0])
    x = xnodes[hit_i]
    delta_linear = 1
    for root in roots[1:]:
        delta_linear = delta_linear*(1-root*x) % P
    residue = ci[hit_i]*pow(delta_linear, -1, P) % P
    check('minimal_unmarked_residue', residue == ci[hit_i]*alpha[0] % P)
    check('frozen_numerator_ratio', val(Qrev, x) == tags[0])
    for k in range(12):
        lhs = lam([(1-x)*pow(x, k, P) for x in xnodes])
        rhs = lam([(pow(rho, h, P)-rho*x)*pow(rho*x, k, P) for x in xnodes])
        check('finite_pearson_endpoint_identity', lhs == rhs)
    for length in (1, 2, 3, 4, 6, 9):
        def ratio(numerator, denominator):
            return numerator*pow(denominator % P, -1, P) % P
        def an(n):
            if n == 0:
                return ratio(1-pow(rho, length, P), 1-rho)
            return ratio(pow(rho, n, P)*(1-pow(rho, length+n, P)),
                         (1+pow(rho, n, P))*(1-pow(rho, 2*n+1, P)))
        def cn(n):
            if n == 0:
                return 0
            return ratio(-pow(rho, 2*n-1, P)*(1-pow(rho, length-n, P)),
                         (1-pow(rho, 2*n-1, P))*(1+pow(rho, n, P)))
        mass = 1
        for n in range(1, length):
            mass = mass*(1-pow(rho, n, P)) % P
        pm, pc = [1], [(-an(0)) % P, 1]
        qm, qc = [0], [mass]
        for n in range(1, length):
            beta = an(n-1)*cn(n) % P
            check('jacobi_nonterminal_beta_unit', beta != 0)
            factor = [(-an(n)-cn(n)) % P, 1]
            pn = add(mul(factor, pc), scale(pm, -beta))
            qn = add(mul(factor, qc), scale(qm, -beta))
            pm, pc, qm, qc = pc, pn, qc, qn
        wh = prod([[-pow(rho, n, P), 1] for n in range(length)])
        check('jacobi_terminal_denominator', pc == wh)
        check('jacobi_terminal_numerator', qc == [0]*(length-1)+[mass])
        check('jacobi_terminal_zero', cn(length) == 0)
    # Arbitrary polynomial states only: this is not a native input counterfamily.
    left, right, a = [0, 2, 3, 4], [1, 2, 3, 4], 7
    check('top_two_do_not_close_arbitrary_states', left[-2:] == right[-2:] and val(left, a) != val(right, a))
    return {'field_prime':P, 'q':q, 'h':h, 'checks':checks, 'total_checks':sum(checks.values()),
            'verdict':'PASS', 'scope':'Finite exact identity diagnostics, including zero/repeated nonhit cases. Not native coverage, a complexity proof, or a factoring-success test.'}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'verdict':result['verdict'], 'total_checks':result['total_checks']}))
