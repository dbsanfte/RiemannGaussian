import itertools
import unittest
from gcd_kmp import match, cyclic_match, automorphism_matches

P, Q, N = 5, 7, 35

def local_occurrences(pattern, text, p):
    return tuple(i for i in range(len(text)-len(pattern)+1)
                 if all((text[i+k]-x) % p == 0 for k,x in enumerate(pattern)))

def local_cyclic(a, b, p):
    if not a:
        return (0,)
    return tuple(r for r in range(len(a))
                 if all((b[k]-a[(k+r)%len(a)]) % p == 0 for k in range(len(a))))

def crt(a,b):
    return (a + P*((b-a)*pow(P,-1,Q) % Q)) % N

class TestKMP(unittest.TestCase):
    def check(self, result, expected_p, expected_q):
        if result.factor is not None:
            self.assertTrue(1 < result.factor < N)
            self.assertEqual(N % result.factor, 0)
            self.assertEqual(result.positions, ())
        else:
            self.assertEqual(result.positions, expected_p)
            self.assertEqual(result.positions, expected_q)
        if expected_p != expected_q:
            self.assertIsNotNone(result.factor)

    def test_exact_small_cyclic_oracle(self):
        alphabet = (0,1,5,7)
        for d in range(1,4):
            for values in itertools.product(alphabet, repeat=2*d):
                a,b = values[:d],values[d:]
                r = cyclic_match(N,a,b)
                self.check(r,local_cyclic(a,b,P),local_cyclic(a,b,Q))
                self.assertLessEqual(r.comparisons,6*d)

    def test_later_coordinates_and_different_local_shifts(self):
        a=(0,1,2,3)
        for b in ((0,1,2,crt(3,4)),
                  tuple(crt(a[k],a[(k+1)%4]) for k in range(4))):
            r=cyclic_match(N,a,b)
            self.check(r,local_cyclic(a,b,P),local_cyclic(a,b,Q))
            self.assertIsNotNone(r.factor)
        # The latter has a whole local match at distinct shifts, not a sparse
        # single-coordinate mismatch assumption.
        b=tuple(crt(a[k],a[(k+1)%4]) for k in range(4))
        self.assertEqual(local_cyclic(a,b,P),(0,))
        self.assertEqual(local_cyclic(a,b,Q),(1,))

    def test_repeated_equal_and_long_failure_chains(self):
        for d in (1,2,17,513):
            for a,b in (([1]*d,[1]*d),([0]*(d-1)+[1],[0]*(d-1)+[2])):
                r=cyclic_match(N,a,b)
                self.check(r,local_cyclic(a,b,P),local_cyclic(a,b,Q))
                self.assertLessEqual(r.comparisons,6*d)
        r=match(N,[1,2,1],[1,2,1,2,1])
        self.check(r,(0,2),(0,2))
        self.assertLessEqual(r.comparisons,2*(3+5))
        # A proper gcd can arise during prefix-table construction itself.
        self.assertEqual(match(N,[0,5],[]).factor,5)

    def test_empty_invalid_and_signed_representatives(self):
        self.assertEqual(match(N,[],[1,2]).positions,(0,1,2))
        self.assertEqual(cyclic_match(N,[],[]).positions,(0,))
        self.assertEqual(match(N,[1],[]).positions,())
        self.assertEqual(cyclic_match(N,[-1,36],[34,1]).positions,(0,))
        for args in ((1,[],[]),(True,[],[]),(N,[1.0],[])):
            with self.assertRaises(ValueError): match(*args)
        with self.assertRaises(ValueError): cyclic_match(N,[1],[])

    def test_automorphism_oracle_and_zero_coefficient(self):
        m,g=7,3
        a=(4,0,1,2,3,1,0)
        for jp,jq in itertools.product(range(1,m),repeat=2):
            b=tuple(crt(a[(k*pow(jp,-1,m))%m],
                        a[(k*pow(jq,-1,m))%m]) for k in range(m))
            r=automorphism_matches(N,m,g,a,b)
            def oracle(p):
                return tuple(j for j in range(1,m) if all(
                    (b[k]-a[k*pow(j,-1,m)%m])%p==0 for k in range(m)))
            if r.factor is None:
                self.assertEqual(set(r.positions),set(oracle(P)))
                self.assertEqual(set(r.positions),set(oracle(Q)))
            else:
                self.assertTrue(1<r.factor<N and N%r.factor==0)
            if oracle(P)!=oracle(Q): self.assertIsNotNone(r.factor)
            self.assertLessEqual(r.comparisons,6*(m-1)+1)
        b=list(a);b[0]+=P
        self.assertEqual(automorphism_matches(N,m,g,a,b).factor,P)
        b[0]=a[0]+1
        self.assertEqual(automorphism_matches(N,m,g,a,b).positions,())
        for bad_m,bad_g in ((9,2),(7,2),(2,1)):
            with self.assertRaises(ValueError):
                automorphism_matches(N,bad_m,bad_g,a,a)

if __name__=='__main__': unittest.main()
