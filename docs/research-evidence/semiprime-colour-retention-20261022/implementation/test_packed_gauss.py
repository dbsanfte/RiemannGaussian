"""Small exact controls; hidden prime inputs occur ONLY in test oracles."""
import json
import random
import unittest
from math import gcd
from packed_gauss import (PackedGauss, PublicFactor, cyclic_mul,
                          all_divisor_monomial_extract, divisors, PACK_BACKEND)


def direct_gauss(pg, a):
    # FULL test-only X^k=1, Phi_ell(Z)=0 carrier. Z^(ell-1)=-sum lower.
    out = [[0]*(pg.ell-1) for _ in range(pg.k)]
    for t in range(1, pg.ell):
        x = a*pg.logs[t] % pg.k
        if t == pg.ell-1:
            out[x] = [(v-1) % pg.N for v in out[x]]
        else:
            out[x][t] = (out[x][t]+1) % pg.N
    return out


def direct_mul(pg, A, B):
    out = [[0]*(pg.ell-1) for _ in range(pg.k)]
    for i, row in enumerate(A):
        for t, a in enumerate(row):
            for j, col in enumerate(B):
                for s, b in enumerate(col):
                    if not a or not b:
                        continue
                    x, z = (i+j) % pg.k, (t+s) % pg.ell
                    if z == pg.ell-1:
                        out[x] = [(v-a*b) % pg.N for v in out[x]]
                    else:
                        out[x][z] = (out[x][z]+a*b) % pg.N
    return out


def direct_power(pg, A, exponent):
    out = [[0]*(pg.ell-1) for _ in range(pg.k)]
    out[0][0] = 1
    while exponent:
        if exponent & 1:
            out = direct_mul(pg, out, A)
        A = direct_mul(pg, A, A)
        exponent //= 2
    return out


def coefficient_embed(pg, C):
    return [[c]+[0]*(pg.ell-2) for c in C]


def crt_vector(p, q, vp, vq):
    return [(a+p*((b-a)*pow(p, -1, q) % q)) % (p*q)
            for a, b in zip(vp, vq)]


class ConvolutionControls(unittest.TestCase):
    def test_packing_carries_and_random(self):
        rng = random.Random(20261022)
        for N in [3, 35, 257, 65537, (1 << 130)+51]:
            for k in [1, 2, 3, 8, 17]:
                for a, b in [([N-1]*k, [N-1]*k),
                             ([rng.randrange(N) for _ in range(k)],
                              [rng.randrange(N) for _ in range(k)])]:
                    self.assertEqual(cyclic_mul(a, b, N),
                                     cyclic_mul(a, b, N, 'quadratic'))


class GaussControls(unittest.TestCase):
    def test_full_phi_carrier_and_every_exception(self):
        # Includes k=1, proper-order characters, and prime/composite k.
        for N, ell, k in [(35, 2, 1), (35, 3, 1), (35, 3, 2), (77, 5, 4),
                          (55, 7, 6), (55, 7, 3)]:
            pg = PackedGauss(N, ell, k)
            for a in range(k):
                for b in range(k):
                    c = pg.product_constant(a, b)
                    lhs = direct_mul(pg, direct_gauss(pg, a), direct_gauss(pg, b))
                    rhs = direct_mul(pg, coefficient_embed(pg, c),
                                     direct_gauss(pg, (a+b) % k))
                    self.assertEqual(lhs, rhs, (N, ell, k, a, b))
            for E in [0, 1, 2, 3, 4, 5, 6, 9, 13]:
                C = pg.quotient(E)
                self.assertEqual(sum(C) % N, pow(-1, E+1, N))
                self.assertEqual(direct_power(pg, direct_gauss(pg, 1), E),
                                 direct_mul(pg, coefficient_embed(pg, C),
                                            direct_gauss(pg, E % k)),
                                 (N, ell, k, E))

    def test_large_exponent_cocycle_and_quadratic_backend(self):
        pg = PackedGauss(101*103, 17, 8)
        a, b = 123, 77
        Ca, Cb, Cab = pg.quotient(a), pg.quotient(b), pg.quotient(a*b)
        rho_a = [0]*pg.k
        for i, c in enumerate(Cb):
            rho_a[a*i % pg.k] = (rho_a[a*i % pg.k]+c) % pg.N
        power, term, e = pg.one(), Ca, b
        while e:
            if e & 1:
                power = pg.mul(power, term)
            term = pg.mul(term, term)
            e //= 2
        self.assertEqual(Cab, pg.mul(power, rho_a))
        slow = PackedGauss(pg.N, pg.ell, pg.k, backend='quadratic')
        self.assertEqual(pg.quotient(103), slow.quotient(103))

    def test_input_unit_guards(self):
        with self.assertRaises(PublicFactor) as context:
            PackedGauss(15, 7, 6)
        self.assertEqual(context.exception.factor, 3)
        for args in [(21, 7, 6), (35, 9, 2), (35, 7, 4)]:
            with self.assertRaises(ValueError):
                PackedGauss(*args)
        with self.assertRaises(ValueError):
            PackedGauss(35, 3, 2).quotient(-1)


class RestrictionControls(unittest.TestCase):
    def test_every_divisor_and_parent_fold_cost(self):
        k = 60
        C = [0]*k
        C[47] = 1
        result = all_divisor_monomial_extract(35, C)
        self.assertIsNone(result['factor'])
        self.assertEqual([r['divisor'] for r in result['records']], divisors(k))
        for r in result['records']:
            self.assertEqual(r['status'], 'GLOBAL_MONOMIAL')
            self.assertEqual(r['position'], 47 % r['divisor'])
        self.assertLessEqual(result['folding_additions'], 3*sum(divisors(k)))

    def test_monomial_dense_and_different_positions(self):
        p, q, k = 5, 7, 6
        mono = [0]*k
        mono[2] = 1
        dense_p = [1, 1, 1, 1, 1, 1]  # sum=1 mod5
        dense_q = [1, 1, 1, 1, 1, 3]  # sum=1 mod7
        for vp, vq in [(mono, dense_q), (dense_p, mono),
                       (mono, [1, 0, 0, 0, 0, 0])]:
            C = crt_vector(p, q, vp, vq)
            result = all_divisor_monomial_extract(p*q, C)
            g = result['factor']
            self.assertIn(g, [p, q])
            d, r = result['divisor'], result['position']
            folded = [sum(C[i] for i in range(s, k, d)) % (p*q) for s in range(d)]
            self.assertTrue(all(c % g == 0 for s, c in enumerate(folded) if s != r))
            self.assertEqual(folded[r] % g, 1)

    def test_factor_only_after_proper_divisor_fold(self):
        # Both top-level vectors dense; modulo X^2-1 only the P vector is monomial.
        C = crt_vector(5, 7, [1, 1, -1, 0], [2, 0, 0, -1])
        result = all_divisor_monomial_extract(35, C)
        self.assertEqual(result['factor'], 5)
        self.assertEqual(result['divisor'], 2)
        self.assertEqual(result['records'][0]['status'], 'BOTH_LOCALLY_NONMONOMIAL')

    def test_dense_same_no_factor_and_invalid_normalization(self):
        result = all_divisor_monomial_extract(35, [2, -1, 0, 0, 0, 0])
        self.assertIsNone(result['factor'])
        self.assertEqual(result['records'][-1],
                         {'divisor': 1, 'status': 'GLOBAL_MONOMIAL', 'position': 0})
        for record in result['records'][:-1]:
            self.assertEqual(record['status'], 'BOTH_LOCALLY_NONMONOMIAL')
        with self.assertRaises(ValueError):
            all_divisor_monomial_extract(35, [0, 0])


if __name__ == '__main__':
    print(json.dumps({'packing_backend': PACK_BACKEND, 'scope': 'exact controls only'}))
    unittest.main(verbosity=2)
