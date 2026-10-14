"""Check full-window coverage against exact rational cell/ramp integrals."""
from fractions import Fraction as Q
import unittest
import flint
from prime_twist_coverage import square_prefix,whole_moment,real


class CoverageContracts(unittest.TestCase):
    def test_complete_moments_against_exact_rational_simpson_and_ramps(self):
        flint.ctx.prec=384
        values=[Q(0),Q(1,3),Q(-2),Q(0),Q(3,7),Q(-5,6),Q(2),Q(-1),Q(4,3)]
        native=list(map(real,values));prefix=square_prefix(native)
        for X in range(1,5):
            A2,D,off=whole_moment(native,prefix,X)
            integral=sum(((values[n]**2+4*((values[n]+values[n+1])/2)**2+values[n+1]**2)/6 for n in range(X,2*X)),Q(0))
            diag=Q(0)
            for n in range(1,2*X+1):
                def ramp(t):return min(Q(1),max(Q(0),t-n+1))
                knn=sum(((ramp(Q(k))**2+4*ramp(Q(2*k+1,2))**2+ramp(Q(k+1))**2)/6 for k in range(X,2*X)),Q(0))
                diag+=(values[n]-values[n-1])**2*knn
            self.assertTrue(A2.contains(real(integral)))
            self.assertTrue(D.contains(real(diag)))
            self.assertTrue(off.contains(real(integral-diag)))

    def test_shared_zero_endpoint_and_a_single_signed_ramp(self):
        flint.ctx.prec=384
        values=[real(0),real(0),real(-3),real(-3),real(-3)]
        A2,D,off=whole_moment(values,square_prefix(values),1)
        self.assertTrue(A2.contains(3));self.assertTrue(D.contains(3));self.assertTrue(off.contains(0))


if __name__=="__main__":unittest.main()
