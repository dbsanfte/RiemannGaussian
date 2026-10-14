import unittest
from fractions import Fraction as Q
import convolution_control_checks as c


class ConvolutionControls(unittest.TestCase):
    def test_actual_factorization_inverse_and_pointwise_sign(self):
        a=c.actual_sequences(40)
        self.assertEqual(a['c'][1:9],[1,-2,-2,2,-2,4,-2,-2])
        self.assertEqual(c.convolution(a['mu'],a['lambda']),list(map(Q,a['c'])))
        self.assertEqual(c.convolution(a['c'],a['h']),[0,1]+[0]*39)
        self.assertTrue(all(a['c'][n]==a['lambda'][n]*a['h'][n] for n in range(1,41)))

    def test_counterfeit_cubic_energy_with_all_inverse_algebra(self):
        a=c.one_prime_sequences(128)
        self.assertEqual(c.convolution(a['c'],a['h']),[0,1]+[0]*127)
        C=c.prefixes(a['c'])
        for K in range(7):
            r=c.dyadic_one_prime_energy(K);X=r['X']
            self.assertEqual(C[X],r['prefix'])
            self.assertEqual(sum(v*v for v in C[X:2*X]),r['energy'])
            if K>=2:self.assertGreater(r['defect'],0)
        self.assertGreater(c.dyadic_one_prime_energy(8)['energy'],Q(2**24))

    def test_fresh_prime_control_matches_entire_prefix(self):
        actual=c.actual_sequences(80);modified=c.modified_prime_sequences(80,43,43)
        self.assertEqual(actual['c'][:43],modified['c'][:43])
        self.assertEqual(actual['h'][:43],modified['h'][:43])
        self.assertNotEqual(actual['c'][43],modified['c'][43])
        self.assertEqual(c.convolution(modified['c'],modified['h']),[0,1]+[0]*79)

    def test_involution_actual_and_counterfeit(self):
        actual=c.actual_sequences(40);fake=c.one_prime_sequences(40)
        f=[0]+[n*n-3*n+1 for n in range(1,41)]
        for a in (actual,fake):
            T=lambda v:c.signed_involution(v,a['h'],actual['lambda'])
            self.assertEqual(T(T(f)),f)

    def test_complete_coefficient_and_prefix_gram(self):
        a=c.actual_sequences(63)
        g=c.coefficient_gram(a['c'],a['h'],63)
        self.assertEqual(g['full'],1);self.assertEqual(g['signed_cross'],1-g['diagonal'])
        for X in (1,2,4,8,16):
            r=c.prefix_gram_profile(a['c'],a['h'],X)
            self.assertEqual(r['parent']['full'],X);self.assertEqual(r['child']['full'],2*X)
            self.assertEqual(r['delta']['full'],-2*X)
            self.assertEqual(r['delta']['C_energy']+r['delta']['other_diagonal']+r['delta']['signed_cross'],-2*X)
            self.assertGreaterEqual(r['parent']['potential'],0)
            self.assertEqual(r['potential_innovation'],Q(-2*X-r['delta']['signed_cross'],4*X*X))

    def test_resource_missing_is_not_projected_success(self):
        a=c.actual_sequences(31)
        r=c.prefix_gram_profile(a['c'],a['h'],8,max_terms=1)
        self.assertEqual(r['status'],'missing')
        self.assertNotIn('parent',r)
        with self.assertRaises(ValueError):c.prefix_gram_profile([0,1],[0,1],2)


if __name__=='__main__':unittest.main()
