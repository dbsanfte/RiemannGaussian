"""Bounded exact algebra/control tests, not empirical factoring evidence."""
import unittest
from math import gcd
from composite_colours import (catalog, canonical_rows, auxiliary_prime,
    ceil_sixth_root, factor_prime_powers, legendre_unit, preprocess,
    screen_public_primes, sieve)


class CompositeColourTests(unittest.TestCase):
    def test_exact_roots_and_selector(self):
        for a in (1,2,3,7,20):
            self.assertEqual(ceil_sixth_root(a**6),a)
            if a > 1:
                self.assertEqual(ceil_sixth_root(a**6-1),a)
            self.assertEqual(ceil_sixth_root(a**6+1),a+1)
        for N in (35,77,1009,1000003):
            ell,ledger = auxiliary_prime(N)
            flags = sieve(ell)
            self.assertEqual(ell % 4,3)
            self.assertTrue(flags[ell])
            self.assertGreater(ell,2*ceil_sixth_root(N))
            self.assertFalse(any(flags[p] and p%4 == 3
                                 for p in range(ledger['threshold']+1,ell)))
            self.assertGreaterEqual(((ell-1)//2)**6,N)

    def test_composite_palettes_exact_including_nonunits(self):
        for m in (9,15,27,45,75):
            cat = catalog(m)
            sq = {t*t % m for t in range(m)}
            primes = [p for p,e,n in cat['factorization']]
            for u in range(1,m):
                if gcd(u,m) == 1:
                    colour = tuple(legendre_unit(u,p) for p in primes)
                    self.assertEqual(set(cat['palettes'][colour]),
                                     {u*r % m for r in sq})
            self.assertTrue(all(values == sorted(set(values)) and 0 in values
                                for values in cat['palettes'].values()))
            expected = 1
            for p,e,n in cat['factorization']:
                count = 2+sum((p-1)*p**(e-v-1)
                              for v in range(0,e,2))
                expected *= count
            self.assertEqual(cat['total_descriptors'],expected)
            self.assertLessEqual(cat['local_scans'],m)
            self.assertLessEqual(cat['crt_pair_visits'],2*expected)

    def test_canonical_masks_and_bounded_antipodes(self):
        for m,N in ((9,35),(15,77),(27,55),(45,77)):
            cat = catalog(m)
            rows = canonical_rows(N,m)
            byj = {row['j']:row for row in rows}
            for row in rows:
                a,b,c,j = (row[k] for k in ('a','b','c','j'))
                self.assertEqual(m*m*c-j*m*b+j*j*a,N)
                invj = pow(j,-1,m)
                image = {(a*h*h+b*h+c)*invj % m for h in range(m)}
                translated = {(row['kappa']+r) % m
                              for r in cat['palettes'][row['colour']]}
                self.assertEqual(image,translated)
                mate = byj[m-j]
                self.assertEqual(mate['a'],a)
                self.assertIn(row['v']+mate['v'],(-2*m**3,-m**3,0))
                self.assertEqual(row['e']+mate['e'],
                                 2*N+2*a+row['v']+mate['v'])

    def test_true_tag_integer_coverage(self):
        for m,P,Q in ((9,5,7),(15,7,11),(27,5,11),(45,7,11)):
            N = P*Q
            row = next(r for r in canonical_rows(N,m) if r['j'] == P%m)
            numer = row['a']*P+Q+row['ell']
            self.assertEqual(numer % (m*m),0)
            I = numer//(m*m)
            palette = catalog(m)['palettes'][row['colour']]
            self.assertIn((I-row['kappa'])%m,palette)

    def test_individual_screens_repair_combined_saturation(self):
        # gcd(15,3*5)=15 is saturated; individual prime screen returns3.
        result = screen_public_primes(15,31,factor_prime_powers(15))
        self.assertEqual(result['status'],'FACTOR')
        self.assertEqual(result['factor'],3)
        same = screen_public_primes(7,7,[])
        self.assertEqual(same['status'],'INPUT_EQUALS_PUBLIC_PRIME')
        out = preprocess(1009)
        self.assertEqual(out['screen']['status'],'COPRIME')
        self.assertEqual(out['ledger']['long_H_values_computed'],0)
        self.assertEqual(gcd(out['N'],out['ell']*out['m']),1)


if __name__ == '__main__':
    unittest.main()
