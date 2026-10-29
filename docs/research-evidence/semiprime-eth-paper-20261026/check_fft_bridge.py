#!/usr/bin/env python3
"""Finite identity checks for the proposed reduction, not a factorer or D.1.

The general proof is in implications.md. These checks catch port-order,
twiddle, inverse-normalization and carry mistakes in that proof's formulas.
No tensor contraction algorithm from the supplied paper is implemented.
"""

import json


def direct_dft(values, root, modulus):
    n = len(values)
    return [sum(x * pow(root, j * k, modulus)
                for j, x in enumerate(values)) % modulus for k in range(n)]


def macro_dft(values, root, modulus):
    n = len(values)
    a = n.bit_length() - 1
    assert n == 1 << a
    r, t = 1 << (a // 2), 1 << (a - a // 2)
    middle = [[sum(values[j1 + r * j2] * pow(root, r * j2 * k2, modulus)
                   for j2 in range(t)) % modulus
               for k2 in range(t)] for j1 in range(r)]
    result = [0] * n
    for k2 in range(t):
        for k1 in range(r):
            result[k2 + t * k1] = sum(
                middle[j1][k2] * pow(root, j1 * k2 + t * j1 * k1, modulus)
                for j1 in range(r)) % modulus
    return result


def parameters(bits):
    n = 1
    while n * n < 16 * bits:
        n *= 2
    b = n // 4
    d = (bits + b - 1) // b
    return n, b, d


def convolution(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            out[i + j] += x * y
    return out


def run():
    checks = dict(principal_root_sums=0, basis_transform_equalities=0,
                  inverse_equalities=0, exact_convolutions=0,
                  integer_carry_equations=0, graph_parameter_checks=0)
    for n in (8, 16, 32, 64):
        modulus, root = (1 << n) + 1, 4
        inverse_root, inverse_n = pow(root, -1, modulus), pow(n, -1, modulus)
        for frequency in range(1, n):
            assert sum(pow(root, frequency * j, modulus) for j in range(n)) % modulus == 0
            checks['principal_root_sums'] += 1
        # Agreement on every basis vector checks all linear input combinations.
        for position in range(n):
            basis = [int(j == position) for j in range(n)]
            transformed = macro_dft(basis, root, modulus)
            assert transformed == direct_dft(basis, root, modulus)
            checks['basis_transform_equalities'] += 1
            recovered = [x * inverse_n % modulus
                         for x in macro_dft(transformed, inverse_root, modulus)]
            assert recovered == basis
            checks['inverse_equalities'] += 1
        arbitrary = [(13 * j * j + (1 << n) * (j % 3)) % modulus for j in range(n)]
        assert macro_dft(arbitrary, root, modulus) == direct_dft(arbitrary, root, modulus)

    for bits in (2, 3, 7, 15, 31, 63, 127, 255):
        n, b, d = parameters(bits)
        base, modulus, width = 1 << b, (1 << n) + 1, n + 1
        assert d <= n // 4 and 2 * d - 2 < n
        assert d * base * base < modulus
        # Exact edges for integrated digit/OR vertices and integer-carry vertices.
        original_edges = (10 * n - 1) * width + 2 * (n - 1)
        bipartite_edges = 2 * original_edges
        a = n.bit_length() - 1
        max_degree = max(2 * (1 << ((a + 1) // 2)) * width, 3 * width, width + 2)
        s = 1024 * bits
        assert bipartite_edges <= 100 * s
        assert max_degree ** 10 <= s ** 9
        assert 2 * bits + 1 <= s
        checks['graph_parameter_checks'] += 1
        top_bits = bits - b * (d - 1)
        bounds = [base - 1] * (d - 1) + [(1 << top_bits) - 1]
        vector_pairs = [
            (bounds, bounds),
            ([min(v, (3 * i + 1)) for i, v in enumerate(bounds)],
             [min(v, (7 * i + 2)) for i, v in enumerate(bounds)]),
            ([0] * d, bounds),
        ]
        for left, right in vector_pairs:
            padded_left, padded_right = left + [0] * (n - d), right + [0] * (n - d)
            lf, rf = macro_dft(padded_left, 4, modulus), macro_dft(padded_right, 4, modulus)
            spectral_product = [x * y % modulus for x, y in zip(lf, rf)]
            recovered = [x * pow(n, -1, modulus) % modulus for x in
                         macro_dft(spectral_product, pow(4, -1, modulus), modulus)]
            exact = convolution(left, right)
            assert recovered == exact + [0] * (n - len(exact))
            checks['exact_convolutions'] += 1
            product = sum(v * base ** i for i, v in enumerate(left)) * sum(
                v * base ** i for i, v in enumerate(right))
            carry = 0
            for i, coefficient in enumerate(recovered):
                digit = (product >> (b * i)) & (base - 1)
                next_carry, remainder = divmod(coefficient + carry - digit, base)
                assert remainder == 0 and 0 <= next_carry < d * base
                assert coefficient + carry == digit + base * next_carry
                carry = next_carry
                checks['integer_carry_equations'] += 1
            assert carry == 0
    return dict(result='PASS', scope='Finite FFT/carry/parameter identities only',
                paper_tensor_algorithm_implemented=False,
                factoring_algorithm_implemented=False,
                source_theorem_certified=False, checks=checks)


if __name__ == '__main__':
    print(json.dumps(run(), indent=2))
