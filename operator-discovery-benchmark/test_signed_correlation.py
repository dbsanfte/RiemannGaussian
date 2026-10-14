"""Independent direct integrations check the universal diagonal rewrite."""
from fractions import Fraction as Q
import random
import unittest
from signed_correlation import square_prefix,diagonal_moment


def independent_diagonal(mu,b,p,X):
    result=Q(0)
    for n in range(1,2*X+1):
        points=sorted({X,2*X}|{b**j*k for j in range(len(p)) for k in (n-1,n) if X<b**j*k<2*X})
        for left,right in zip(points,points[1:]):
            def f(t):
                return sum((c*max(Q(0),min(Q(1),Q(t,b**j)-n+1)) for j,c in enumerate(p)),Q(0))
            x,y=f(left),f(right)
            result+=mu[n]**2*Q(right-left,3)*(x*x+x*y+y*y)
    return result


class SignedCorrelationContracts(unittest.TestCase):
    def test_exact_boundary_and_signed_diagonal_against_direct_ramps(self):
        rng=random.Random(4711)
        for b in (2,3,7):
            for X in (1,2,3,7,13,31):
                mu=[0]+[rng.choice([-1,0,1]) for _ in range(2*X)]
                p=[Q(1),Q(-7,8),Q(3,4),Q(-1,2)]
                counts,weighted=square_prefix(mu)
                actual=diagonal_moment(mu,counts,weighted,b,p,X)
                self.assertEqual(actual,independent_diagonal(mu,b,p,X))
                self.assertLessEqual(actual,2*sum(abs(c) for c in p)**2*X*X)

    def test_positive_control_has_large_signed_off_diagonal(self):
        X=100; mu=[0]+[1]*(2*X); counts,weighted=square_prefix(mu)
        diagonal=diagonal_moment(mu,counts,weighted,2,[1],X)
        total=Q((2*X)**3-X**3,3)
        self.assertGreater(total-diagonal,X*X)


if __name__=="__main__": unittest.main()
