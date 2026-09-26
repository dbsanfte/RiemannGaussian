"""Optional Gauss rule for the literal finite-window factorial density.

This changes a numerical integration rule, not the Riesz carrier or any
mask. The rule integrates u^(N+1) exp(-u*T) T^N/N! on [39N/20,203N/100].
It is not a bound for the remaining, varying-amplitude integrand.

Centering Y=u*T at a=N+1, with X=(Y-a)/sqrt(a), avoids subtracting enormous
raw gamma moments. Integration by parts gives the exact finite-window
recurrence

 M_(k+1) = k M_(k-1) + k/sqrt(a) M_k
           - [(1+x/sqrt(a))*x^k*f_X(x)]_left^right.

Both exterior boundary terms are retained. Stieltjes recurrence coefficients
and bracketed Gaussian nodes/Christoffel weights are computed as balls.
Checks of moments through degree 2*q-1 are numerical regressions, not a Lean
quadrature theorem. Keep outside ordinary CI and certificate verification.
"""
from flint import arb, arb_poly
from scipy.linalg import eigh_tridiagonal


def centered_moments(n, u, lo, hi, count):
    a, sd = arb(n+1), arb(n+1).sqrt()
    left, right = (u*lo-a)/sd, (u*hi-a)/sd
    mass = (u*lo).gamma_upper(n+1, regularized=True)-(u*hi).gamma_upper(n+1, regularized=True)
    assert mass > 0

    def boundary(x):
        y = a+sd*x
        density = (sd.log()+n*y.log()-y-arb.fac_ui(n).log()).exp()
        return (1+x/sd)*density

    bl, br = boundary(left), boundary(right)
    moments = [mass]
    for k in range(count-1):
        moments.append((k*moments[k-1] if k else arb(0))+k/sd*moments[k]
                       + bl*left**k-br*right**k)
    return moments, left, right, a, sd


def gamma_rule(n, u, lo, hi, q):
    """Return (T,weight) nodes for the unrenormalized truncated gamma measure."""
    assert n >= 1 and q >= 1 and 0 < lo and lo < hi and u > 0
    moments, left, right, a, sd = centered_moments(n, u, lo, hi, 2*q+1)

    def inner(f, g):
        return sum(c*moments[k] for k, c in enumerate((f*g).coeffs()))

    x = arb_poly([0, 1])
    previous, polynomial = arb_poly([]), arb_poly([1])
    previous_norm = arb(1)
    ds, squares, norms = [], [], []
    for j in range(q):
        norm = inner(polynomial, polynomial)
        assert norm > 0, 'Moment precision insufficient for a positive norm'
        diagonal = inner(x*polynomial, polynomial)/norm
        off_square = norm/previous_norm if j else arb(0)
        ds.append(diagonal)
        norms.append(norm)
        if j:
            assert off_square > 0
            squares.append(off_square)
        previous, polynomial = polynomial, (x-diagonal)*polynomial-off_square*previous
        previous_norm = norm
    es = [v.sqrt() for v in squares]
    seeds = eigh_tridiagonal([float(v) for v in ds], [float(v) for v in es], eigvals_only=True)

    def poly(t):
        p0, p1, d0, d1 = arb(1), t-ds[0], arb(0), arb(1)
        for j in range(1, q):
            p0, p1 = p1, (t-ds[j])*p1-squares[j-1]*p0
            d0, d1 = d1, p0+(t-ds[j])*d1-squares[j-1]*d0
        return p1, d1

    out, centered = [], []
    for seed in seeds:
        t = arb(float(seed))
        for _ in range(5):
            v, dv = poly(t)
            t = (t-v/dv).mid()
        v, dv = poly(t)
        from flint import ctx
        eps = arb(2)**(-ctx.prec+48)+4*abs(v/dv).upper()
        for _ in range(64):
            if poly(t-eps)[0]*poly(t+eps)[0] < 0:
                break
            eps *= 2
        else:
            raise ArithmeticError('Gamma-weight Gaussian root not bracketed')
        t = arb(t, eps.upper())
        pol = [arb(1)]
        if q > 1:
            pol.append((t-ds[0])/es[0])
        for j in range(1, q-1):
            pol.append(((t-ds[j])*pol[-1]-es[j-1]*pol[-2])/es[j])
        weight = moments[0]/sum(p*p for p in pol)
        assert left < t and t < right and weight > 0
        centered.append((t, weight))
        out.append(((a+sd*t)/u, weight))
    assert all(out[j][0] < out[j+1][0] for j in range(q-1))
    for k in range(2*q):
        observed = sum(w*t**k for t, w in centered)
        assert observed.overlaps(moments[k]), ('gamma moment', k, observed, moments[k])
    return out, dict(moment_checks=2*q, mass=str(moments[0]),
                     centered_interval=[str(left), str(right)],
                     monic_norms=[str(v) for v in norms])
