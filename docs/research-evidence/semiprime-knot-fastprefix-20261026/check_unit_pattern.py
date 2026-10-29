#!/usr/bin/env python3
"""Exact Laurent-polynomial Fox tests for the T(2,4) unit pattern; stdlib only."""
from itertools import permutations


class Laurent:
    def __init__(self, value=0):
        self.c = ({e: a for e, a in value.items() if a} if isinstance(value, dict)
                  else ({0: value} if value else {}))

    def __add__(self, other):
        other = other if isinstance(other, Laurent) else Laurent(other)
        result = self.c.copy()
        for e, a in other.c.items():
            result[e] = result.get(e, 0) + a
        return Laurent(result)

    __radd__ = __add__

    def __neg__(self):
        return Laurent({e: -a for e, a in self.c.items()})

    def __sub__(self, other):
        return self + (-other if isinstance(other, Laurent) else -Laurent(other))

    def __mul__(self, other):
        other = other if isinstance(other, Laurent) else Laurent(other)
        result = {}
        for e, a in self.c.items():
            for f, b in other.c.items():
                result[e + f] = result.get(e + f, 0) + a * b
        return Laurent(result)

    __rmul__ = __mul__

    def __eq__(self, other):
        return self.c == (other.c if isinstance(other, Laurent) else Laurent(other).c)


def matrix(rows):
    return [[x if isinstance(x, Laurent) else Laurent(x) for x in row] for row in rows]


I = matrix([[1, 0], [0, 1]])
ZERO = matrix([[0, 0], [0, 0]])


def add(a, b):
    return [[a[i][j] + b[i][j] for j in range(len(a[0]))] for i in range(len(a))]


def scale(a, s):
    return [[x * s for x in row] for row in a]


def mul(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(len(b))), Laurent())
             for j in range(len(b[0]))] for i in range(len(a))]


def inv_sl2(a):
    assert determinant(a) == 1
    return [[a[1][1], -a[0][1]], [-a[1][0], a[0][0]]]


def determinant(a):
    result = Laurent()
    for p in permutations(range(len(a))):
        inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))
        term = Laurent((-1) ** inversions)
        for i, j in enumerate(p):
            term = term * a[i][j]
        result = result + term
    return result


def fox(word, images, generator):
    prefix, derivative = I, ZERO
    for letter, sign in word:
        image = images[letter] if sign == 1 else inv_sl2(images[letter])
        if letter == generator:
            derivative = add(derivative, prefix if sign == 1 else scale(mul(prefix, image), -1))
        prefix = mul(prefix, image)
    return derivative, prefix


def main():
    z, zi = Laurent({1: 1}), Laurent({-1: 1})
    a, b = matrix([[z, 0], [0, zi]]), matrix([[0, 1], [-1, 0]])
    c = mul(a, b)
    assert mul(c, c) == scale(I, -1)
    assert mul(mul(mul(a, b), inv_sl2(a)), inv_sl2(b)) == matrix([[z*z, 0], [0, zi*zi]])
    word_ac = [('a', 1), ('c', 1), ('c', 1), ('a', -1), ('c', -1), ('c', -1)]
    da, relator = fox(word_ac, {'a': a, 'c': c}, 'a')
    dc, _ = fox(word_ac, {'a': a, 'c': c}, 'c')
    assert relator == I
    assert da == scale(I, 2)
    assert dc == mul(add(a, scale(I, -1)), add(I, c))
    assert determinant(add(c, scale(I, -1))) == 2
    assert determinant(da) == 4
    assert add(mul(da, add(a, scale(I, -1))), mul(dc, add(c, scale(I, -1)))) == ZERO
    word_ab = [('a', 1), ('b', 1), ('a', 1), ('b', 1),
               ('a', -1), ('b', -1), ('a', -1), ('b', -1)]
    da_ab, relator_ab = fox(word_ab, {'a': a, 'b': b}, 'a')
    assert relator_ab == I and determinant(da_ab) == 4
    assert determinant(add(b, scale(I, -1))) == 2
    h = matrix([[z*z, 0], [0, zi*zi]])
    companion_checks = 0
    for coefficient in (-3, 1, 4):
        v = [[coefficient, 0], [-1, 1]]
        expanded = [[Laurent() for _ in range(4)] for _ in range(4)]
        for i in range(2):
            for j in range(2):
                block = add(scale(I, v[i][j]), scale(h, -v[j][i]))
                for r in range(2):
                    for s in range(2):
                        expanded[2*i+r][2*j+s] = block[r][s]
        k = Laurent(1) + coefficient * (z*z + zi*zi - 2)
        assert determinant(expanded) == k*k
        companion_checks += 1
    print('Exact symbolic Laurent ring: Z[z,z^-1]; no floating arithmetic or dependencies.')
    print('Both T(2,4) relators, Fox derivatives, Fox contraction, axis spectrum: passed.')
    print('Per odd pair: numerator determinant=4; meridian determinant=2; base torsion=2.')
    print('Rank 2m direct sum: base torsion=2^m by block multiplicativity.')
    print(f'Companion reciprocal determinant checks passed: {companion_checks}')


if __name__ == '__main__':
    main()
