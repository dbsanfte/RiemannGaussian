"""Compare compressed coverage to complete literal small pair enumeration."""
from fractions import Fraction as Q
from math import gcd
import unittest
import mobius_density_packet_081 as S
import mobius_density_coverage_081 as C
from test_mobius_density_packet_081 import program, mu


class CoverageTests(unittest.TestCase):
    def test_exact_physical_coverage_against_dense_pairs(self):
        p = program(eta='1/3')
        parsed = S.parse(p)
        _, T = S.matrices(parsed)
        for u in (31, 127, 181):
            source = S.Arithmetic(u//2)
            got = C.coverage(p, u, source)
            bank = S.PairBank(p, got['D'], source)
            P, N, *_ = bank.stats[got['D']]
            labels = {(r['a'], r['b']): r['density'] for rows in bank.rows.values() for r in rows}
            f = lambda n: [sum(v for d, v in parsed['kernel'].items() if n <= u//(2**i*d)) for i in range(3)]
            total, removed, diagonal, edges, touched, weighted = Q(0), Q(0), Q(0), 0, 0, Q(0)
            for m in range(1, u//2+1):
                if not mu(m):
                    continue
                diagonal += abs(C.dot(f(m), T, f(m)))
                for n in range(m+1, u//2+1):
                    if not mu(n):
                        continue
                    value = 2*C.dot(f(m), T, f(n))
                    total += abs(value)
                    edges += bool(value)
                    g = gcd(m, n)
                    if (m//g, n//g) in labels:
                        density = labels[m//g, n//g]
                        w = min(Q(1), N/P) if density > 0 else min(Q(1), P/N) if density < 0 else Q(1)
                        removed += w*abs(value)
                        touched += bool(w and value)
                        weighted += w*bool(value)
            self.assertEqual(Q(got['absolute_offdiagonal_coefficient_mass']), total)
            self.assertEqual(Q(got['absolute_diagonal_coefficient_mass']), diagonal)
            self.assertEqual(Q(got['removed_absolute_coefficient_mass']), removed)
            self.assertEqual(got['unordered_nonzero_offdiagonal_pairs'], edges)
            self.assertEqual(got['retained_nonzero_physical_pairs'], touched)
            self.assertEqual(Q(got['weighted_physical_pairs']), weighted)

    def test_actual_prime_frontier_in_original_kernel(self):
        p = program(kernel=[dict(divisor=4, weight='-1'), dict(divisor=5, weight='1'),
            dict(divisor=8, weight='1'), dict(divisor=10, weight='-1')])
        got = C.coverage(p, 1103)['untouched_prime_block']
        self.assertTrue(got['admitted'])
        primes = [n for n in range(1103//5+1, 1103//4+1)
                  if all(n % d for d in range(2, int(n**.5)+1))]
        self.assertEqual(got['prime_count'], len(primes))
        self.assertEqual(Q(got['signed_contribution']), Q(5, 4)*len(primes)*(len(primes)-1))


if __name__ == '__main__':
    unittest.main()
