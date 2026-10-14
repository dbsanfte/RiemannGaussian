import unittest
from fractions import Fraction as Q
from math import isqrt
import fixed_pole_filter_checks as c


def trial_atoms(N):
    mu=[0];lam=[0]
    for n in range(1,N+1):
        rest=n;Omega=omega=0;squarefree=True
        for p in range(2,isqrt(n)+1):
            power=0
            while rest%p==0:rest//=p;power+=1
            if power:Omega+=power;omega+=1;squarefree &= power==1
        if rest>1:Omega+=1;omega+=1
        mu.append((-1)**omega if squarefree else 0);lam.append((-1)**Omega)
    return mu,lam


def conv(a,b):
    return [0]+[sum(a[d]*b[n//d] for d in range(1,n+1) if n%d==0) for n in range(1,len(a))]


class IndependentFixedFilters(unittest.TestCase):
    def test_all_nine_factor_locals_match_complete_convolution(self):
        N=64;mu,lam=trial_atoms(N);structure=c.factor_structure(N)
        for t in c.TARGETS:
            expected=[0,1]+[0]*(N-1)
            for source,count in [(mu,t['r']),(lam,t['l'])]:
                for _ in range(count):expected=conv(expected,source)
            self.assertEqual(c.actual_coefficients(N,**t,structure=structure),expected)

    def test_covariance_is_full_signed_filtered_square(self):
        sums=c.prefix(c.actual_coefficients(31,1,1));matrix=c.covariance(sums,8)
        terms=[(1,1),(2,-2),(3,Q(1,2))]
        G=c.filtered_prefix(sums,terms)
        self.assertEqual(c.filtered_energy(matrix,terms),sum(v*v for v in G[8:16])/64)
        self.assertEqual(matrix[0][1],matrix[1][0])
        with self.assertRaises(RuntimeError):c.covariance(sums,8,max_products=1)

    def test_pole_admission_and_zero_merging(self):
        cert=c.conditional_certificate(1,1,[(1,1),(2,-2),(2,2),(3,1)])
        self.assertEqual(cert['support_size'],2);self.assertTrue(cert['conditional_bridge_admitted'])
        self.assertEqual(cert['minimum_surviving_pole_order'],1)
        self.assertFalse(cert['estimate_proved']);self.assertFalse(cert['RH_proved'])
        self.assertFalse(c.conditional_certificate(1,0,[(1,1),(2,1)])['conditional_bridge_admitted'])
        with self.assertRaises(ValueError):c.canonical_filter([{'divisor':{'moving':2},'weight':'1'}])

    def test_exact_box_minimum_interior_edge_and_singular(self):
        # Two extra variables; positive definite support, unconstrained(-1,-1).
        matrix=[['10','1','1'],['1','1','0'],['1','0','1']]
        r=c.boxed_least_squares(matrix,[2,3],divisors=[1,2,3])
        self.assertEqual(r['exact_weights'],['-1','-1']);self.assertEqual(r['objective'],'8')
        edge=[['100','20','1'],['20','1','0'],['1','0','1']]
        self.assertEqual(c.boxed_least_squares(edge,[2,3],divisors=[1,2,3])['exact_weights'],['-8','-1'])
        singular=[['1','0','0'],['0','1','1'],['0','1','1']]
        self.assertEqual(c.boxed_least_squares(singular,[2,3],divisors=[1,2,3])['status'],'missing')


if __name__=='__main__':unittest.main()
