import unittest
from math import isqrt, comb
import prime_power_pairing as p


def independent_c(n):
    rest=n;omega=0;Omega=0;d=2
    while d*d<=rest:
        if rest%d==0:
            omega+=1
            while rest%d==0:rest//=d;Omega+=1
        d+=1
    if rest>1:omega+=1;Omega+=1
    return (-1)**Omega*(1<<omega)


class PairingTests(unittest.TestCase):
    def test_complete_actual_source_edges_and_residual_for_prespecified_grid(self):
        selectors=[{'kind':'fixed','primes':[]},{'kind':'fixed','primes':[2]},{'kind':'fixed','primes':[2,3,5]},{'kind':'fixed','primes':[5,3,2]},{'kind':'all_primes'},{'kind':'fractional_prime_cutoff','numerator':1,'denominator':3},{'kind':'root_prime_cutoff','order':2}]
        for X in (0,1,2,3,4,7,16,31,64,127,256):
            for selector in selectors:
                outcome=p.matching(X,selector)
                self.assertEqual(outcome['status'],'available',outcome)
                r=outcome['value'];expected=[0]+[independent_c(n) for n in range(1,X+1)]
                self.assertEqual(r['source_coefficients'],expected)
                endpoints=[]
                for edge in r['edges']:
                    lo,hi=edge['lower'],edge['upper'];endpoints.extend([lo,hi])
                    self.assertEqual(hi,lo*edge['prime']);self.assertEqual(expected[lo],-expected[hi])
                    self.assertEqual(edge['lower_exponent']%2,1)
                residual=[x['n'] for x in r['residual']]
                self.assertEqual(sorted(endpoints+residual),list(range(1,X+1)))
                self.assertEqual(len(endpoints),len(set(endpoints)))
                self.assertEqual(r['signed_residual'],sum(expected))
                self.assertEqual(r['unsigned_original_charge'],r['unsigned_cancelled_charge']+r['unsigned_residual_charge'])
                self.assertFalse(r['critical_signed_bound_proved'])

    def test_one_prime_top_boundary_endpoints(self):
        for X in range(101):
            for prime in (2,3,5):
                r=p.matching(X,{'kind':'fixed','primes':[prime]})['value']
                formula=p.fixed_prime_residual_formula(X,prime)
                self.assertEqual(r['signed_residual'],formula['signed_residual'])
                self.assertEqual(r['unsigned_residual_charge'],formula['unsigned_residual_charge'])
        r=p.matching(8,{'kind':'fixed','primes':[2]})['value']
        self.assertIn({'n':8,'c':-2},r['residual']) # odd exponent3; partner16 outside.
        self.assertNotIn({'n':4,'c':2},r['residual']) # paired2,4.

    def test_fixed_core_and_all_prime_obstructions(self):
        for X in (16,31,64,127,256):
            fixed=p.matching(X,{'kind':'fixed','primes':[2,3,5]})['value']
            residual={r['n'] for r in fixed['residual']}
            core={n for n in range(1,X+1) if n%2 and n%3 and n%5}
            self.assertTrue(core<=residual)
            complete=p.matching(X,{'kind':'all_primes'})['value'];residual={r['n'] for r in complete['residual']}
            unavoidable={q for q in complete['actual_primes_through_X'] if q>isqrt(X)}
            self.assertTrue(unavoidable<=residual)
            self.assertGreaterEqual(complete['unsigned_residual_charge'],2*len(unavoidable))

    def test_upper_half_squarefree_linear_obstruction(self):
        for X in (16,31,64,127,256):
            r=p.matching(X,{'kind':'all_primes'})['value']
            residual={row['n'] for row in r['residual']}
            squarefree={n for n in range(X//2+1,X+1) if all(n%(d*d) for d in range(2,isqrt(n)+1))}
            self.assertTrue(squarefree<=residual)
            self.assertGreaterEqual(r['unsigned_residual_charge'],2*len(squarefree))
            cert=p.absolute_residual_obstruction_certificate(X)
            self.assertEqual(cert['linear_bound_applies'],X>=256)
            self.assertFalse(cert['signed_prefix_lower_bound_proved'])
            if X>=256:
                self.assertGreaterEqual(16*len(squarefree),X)
                self.assertGreaterEqual(8*r['unsigned_residual_charge'],X)
                self.assertEqual(cert['unsigned_residual_linear_lower'],{'numerator':X,'denominator':8})
        for X in (256,257,4096,10**20):
            # Pure integer algebra only; no new actual coefficient evaluations.
            cert=p.absolute_residual_obstruction_certificate(X)
            self.assertTrue(cert['exact_threshold_check'])
            self.assertTrue(cert['no_actual_scores_consumed'])

    def test_fixed_two_term_filter_is_exact_p_free_shell(self):
        coefficients=[0]+[independent_c(n) for n in range(1,129)]
        C=[0]
        for value in coefficients[1:]:C.append(C[-1]+value)
        for prime in (2,3,5,7):
            Cp=[0]
            for n in range(1,129):Cp.append(Cp[-1]+(coefficients[n] if n%prime else 0))
            for X in range(129):
                self.assertEqual(C[X]+C[X//prime],Cp[X]-Cp[X//prime])

    def test_exact_central_binomial_prime_count_ingredients(self):
        primes=p.matching(256,{'kind':'all_primes'})['value']['actual_primes_through_X']
        for X in range(16,257):
            n=X//2;Y=2*n;pi=sum(prime<=Y for prime in primes)
            central=comb(Y,n)
            self.assertGreaterEqual(central*(Y+1),1<<Y)
            self.assertLessEqual(central,Y**pi)
            self.assertGreaterEqual(Y,X-1)
            self.assertLessEqual(Y+1,X+1)
        self.assertGreater(1<<7,17) # f(16)>0, no floating logarithm.

    def test_whole_positive_inverse_fake_does_not_have_equal_pair_weights(self):
        fake=[0,1,-4,0,8]
        with self.assertRaises(ValueError):p.edge_certificate(fake,2,2,4)
        with self.assertRaises(ValueError):p.edge_certificate([0]+[independent_c(n) for n in range(1,65)],8,8,64)
        actual=[0]+[independent_c(n) for n in range(1,5)]
        self.assertEqual(p.edge_certificate(actual,2,2,4)['pair_sum'],0)

    def test_invalid_selectors_and_exhaustion_no_partial_result(self):
        for selector in ({'kind':'fixed','primes':[4]},{'kind':'fixed','primes':[2,2]},{'kind':'fixed','primes':[True]},{'kind':'root_prime_cutoff','order':0},{'kind':'fractional_prime_cutoff','numerator':1,'denominator':0}):
            self.assertEqual(p.matching(16,selector)['status'],'invalid')
        for kwargs in ({'operation_budget':10},{'cell_budget':8},{'bit_budget':1}):
            r=p.matching(128,{'kind':'all_primes'},**kwargs)
            self.assertEqual(r['status'],'missing');self.assertIsNone(r['value'])


if __name__=='__main__':unittest.main()
