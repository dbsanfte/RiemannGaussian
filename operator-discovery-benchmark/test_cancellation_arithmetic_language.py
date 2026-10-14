import copy
from fractions import Fraction as Q
import unittest

import grouped_arithmetic_language as L
import cancellation_arithmetic_language as C
from cancellation_prime_transport import build_transport, shell_kernel


def integer(n): return ['int', n]
def var(n): return ['v', n]
def mul(a, b): return ['imul', a, b]
def sub(a, b): return ['isub', a, b]
def maximum(a, b): return ['max', a, b]


def kernel(scale, a, b):
    return maximum(integer(0), sub(mul(integer(2), scale), maximum(scale, maximum(a, b))))


def shell(scale, prime, a, b):
    # Mixed difference assembled from elementary index productions, not a shell primitive.
    pa, pb = mul(integer(prime), a), mul(integer(prime), b)
    return ['iadd', sub(sub(kernel(scale, a, b), kernel(scale, pa, b)), kernel(scale, a, pb)), kernel(scale, pa, pb)]


def transported_program(prime):
    a, b, X = var('a'), var('b'), var('X')
    defect = sub(shell(mul(integer(2), X), prime, a, b), mul(integer(4), shell(X, prime, a, b)))
    domain = ['and', ['not', ['divides', integer(prime), a]], ['not', ['divides', integer(prime), b]]]
    body = ['guard', domain, ['mul', ['embed', defect], ['mul', ['x', a], ['x', b]]]]
    return ['sum', 'a', integer(1), var('N'), ['sum', 'b', integer(1), var('N'), body]]


class Tests(unittest.TestCase):
    def compile(self, expr, X=2, horizon=7, **limits):
        return L.load_poly(C.compile_expression(expr, X, horizon, **limits)['poly'])

    def test_complete_pair_prime_transport_matches_independent_construction(self):
        for X in (1, 2, 3):
            for p in (2, 3, 5):
                built = build_transport(X, p)
                result = self.compile(transported_program(p), X, 4*X-1)
                self.assertEqual(result, L.load_poly(built['transported_defect']))
                # Separately enumerate shell intersections, including both ordered cross terms.
                expected = {}
                for a in range(1, 4*X):
                    for b in range(1, 4*X):
                        if a % p and b % p:
                            w = shell_kernel(2*X, p, a, b)-4*shell_kernel(X, p, a, b)
                            expected = L.add(expected, {tuple(sorted((a, b))): Q(w)})
                self.assertEqual(result, expected)

    def test_exact_partition_has_complement_and_polarization_retains_sign(self):
        full = ['sum', 'a', integer(1), var('N'), ['sum', 'b', integer(1), var('N'),
                ['mul', ['x', var('a')], ['x', var('b')]]]]
        predicate = ['eq', ['gcd', var('a'), var('b')], integer(1)]
        pieces = C.partition(full, predicate)
        self.assertEqual(self.compile(full), L.add(*(self.compile(p) for p in pieces)))
        self.assertNotEqual(self.compile(full), self.compile(pieces[0]))
        left = ['sum', 'n', integer(1), var('X'), ['x', var('n')]]
        right = ['add', ['x', var('N')], ['q', '-2/3']]
        self.assertEqual(self.compile(C.polarization(left, right)), self.compile(['mul', left, right]))

    def test_fractional_cutoffs_and_normalization_are_exact(self):
        for n in (0, 1, 2, 8, 63, 64, 65, 729):
            for a, b in ((1, 2), (1, 3), (1, 6), (2, 3), (3, 2)):
                p = self.compile(['embed', ['root', integer(n), a, b]])
                r = p.get((), Q(0))
                self.assertEqual(r.denominator, 1)
                self.assertLessEqual(int(r)**b, n**a)
                self.assertGreater((int(r)+1)**b, n**a)
        self.assertEqual(self.compile(['ratio', integer(2), integer(6)]), {(): Q(1, 3)})
        self.assertEqual(self.compile(['embed', ['root', integer(0), 0, 6]]), {(): Q(1)})

    def test_guards_types_resources_and_no_implicit_clipping(self):
        shifted = ['sum', 'n', integer(1), var('N'), ['x', ['iadd', var('n'), integer(1)]]]
        with self.assertRaisesRegex(ValueError, 'horizon'):
            self.compile(shifted)
        guarded = copy.deepcopy(shifted)
        guarded[-1] = ['guard', ['lt', var('n'), var('N')], guarded[-1]]
        self.assertEqual(len(self.compile(guarded)), 6)
        with self.assertRaises(ValueError):
            self.compile(['guard', ['eq', integer(0), integer(1)], ['unknown']])
        with self.assertRaises(ValueError): self.compile(['x', integer(True)])
        with self.assertRaises(ValueError): self.compile(['q', '2/4'])
        with self.assertRaises(ValueError): self.compile(['ratio', integer(1), integer(0)])
        with self.assertRaises(ValueError): self.compile(['sum', 'X', integer(1), integer(2), ['q', '1']])
        with self.assertRaises(OverflowError): self.compile(shifted, max_operations=5)
        with self.assertRaises(OverflowError): self.compile(['embed', ['root', integer(2), 1000000, 1]])
        with self.assertRaises(OverflowError):
            self.compile(['guard', ['prime', integer(1000000007)], ['q', '1']], max_operations=100)
        with self.assertRaises(ValueError): self.compile(['q', '1e999999999'])
        with self.assertRaises(OverflowError): self.compile(['q', '9'*10000])
        with self.assertRaises(OverflowError): self.compile(['mul', ['x', integer(1)], ['x', integer(2)]], max_degree=1)

    def test_generic_mixes_are_deterministic_without_scores(self):
        atoms = [['x', integer(1)], ['x', integer(2)], ['q', '1/3']]
        before = copy.deepcopy(atoms)
        candidates = C.enumerate_mixes(atoms)
        self.assertEqual(candidates, C.enumerate_mixes(atoms))
        self.assertEqual(atoms, before)
        self.assertEqual(len(candidates), 12)
        self.assertTrue(any(row['expr'][0] == 'mul' for row in candidates))
        for row in candidates: self.compile(row['expr'])
        with self.assertRaises(OverflowError): C.enumerate_mixes(atoms, max_candidates=2)

    def test_quadratic_multiplier_eliminates_gcd_quartic_without_new_axiom(self):
        from check_grouped_arithmetic import verify_certificate
        spec = dict(kind='gcd_product', a=12, b=18,
                    factors_a=[[2, 2], [3, 1]], factors_b=[[2, 1], [3, 2]])
        norm = dict(kind='norm', n=6, factors=[[2, 1], [3, 1]])
        multiplier = self.compile(['mul', ['x', integer(2)], ['x', integer(3)]], horizon=18)
        reduced = L.add({(12, 18): Q(4)}, {(2, 3): Q(-16)})
        cert = dict(target='c', horizon=18, lhs=L.dump_poly(reduced), squares=[],
                    relations=[dict(spec=spec, multiplier=L.dump_poly(L.constant(1))),
                               dict(spec=norm, multiplier=L.dump_poly(multiplier))])
        self.assertTrue(verify_certificate(cert)['verified'])
        self.assertEqual(reduced, L.add(L.relation(spec, 'c', 18),
                         L.mul(multiplier, L.relation(norm, 'c', 18))))

    def test_growing_prime_range_keeps_signed_product_and_product_horizon(self):
        p, n = var('p'), var('n')
        body = ['mul', ['ratio', integer(1), p], ['mul', ['x', n], ['x', mul(p, n)]]]
        expr = ['sum', 'p', integer(2), ['root', var('X'), 1, 2],
                ['guard', ['prime', p], ['sum', 'n', integer(1), ['idiv', var('N'), p],
                    ['guard', ['eq', ['gcd', p, n], integer(1)], body]]]]
        expected = {}
        for prime in (2, 3, 5, 7):
            for k in range(1, 19//prime+1):
                if k % prime:
                    expected = L.add(expected, {(k, prime*k): Q(1, prime)})
        self.assertEqual(self.compile(expr, X=49, horizon=19), expected)


if __name__ == '__main__': unittest.main()
