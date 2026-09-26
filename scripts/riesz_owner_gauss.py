"""Optional Gaussian rule for the exact conditional owner-order measure.

For 1 <= lo <= hi <= M, integrate against
  sum_{j=lo}^hi binom(M,j) x^(j-1) (1-x)^(M-j) dx, 0 < x < 1.
The 1/x density is included in the measure. Its zeroth moment is the
harmonic sum sum 1/j. Positive moments follow from the beta integral and
the finite hockey-stick identity, with no fitted marginal calibration.

At a least-share r the literal owner variable is p=(1-r)*x. This preserves
the owner/least correlation; it is not an independent owner distribution.
The candidate recurrence is rounded to midpoint coefficients. Independent
moment defects are retained explicitly: no exact Gaussian identity is
claimed for the computed rule. Numerical moment/root enclosures do NOT bound the full varying-amplitude
quadrature, remove physical masks, or prove an arithmetic estimate.
"""
from fractions import Fraction
import math

from flint import arb, arb_poly, ctx, fmpq, fmpz
from scipy.linalg import eigh_tridiagonal


def raw_moments(M, lo, hi, count):
    assert 1 <= lo <= hi <= M and count >= 1
    moments = [sum(arb(1)/j for j in range(lo, hi+1))]
    factor = arb(1)
    for k in range(1, count):
        factor *= arb(k if k > 1 else 1)/(M+k)
        # factor = k! * M! / (M+k)!; divide by k below.
        difference = fmpz.bin_uiui(hi+k, k)-fmpz.bin_uiui(lo+k-1, k)
        moments.append(factor*arb(difference)/k)
    return moments


def centered_moments(M, lo, hi, count):
    raw = raw_moments(M, lo, hi, count)
    center = arb(lo+hi)/(2*M)
    scale = arb(hi-lo+1)/(2*M)
    moments = [sum(arb(fmpz.bin_uiui(k, j))*(-center)**(k-j)*raw[j]
                   for j in range(k+1))/scale**k for k in range(count)]
    return moments, center, scale


def owner_rule(M, lo, hi, q):
    """Positive candidate rule, bracketed roots, and audited moment defects."""
    assert q >= 1
    moments, center, scale = centered_moments(M, lo, hi, 2*q+1)

    def inner(f, g):
        return sum(c*moments[k] for k, c in enumerate((f*g).coeffs()))

    x = arb_poly([0, 1])
    previous, polynomial, previous_norm = arb_poly([]), arb_poly([1]), arb(1)
    diagonals, squares, norms = [], [], []
    for j in range(q):
        norm = inner(polynomial, polynomial)
        assert norm > 0, ('owner moment precision insufficient', j)
        norm = norm.mid()
        diagonal = (inner(x*polynomial, polynomial)/norm).mid()
        off_square = (norm/previous_norm).mid() if j else arb(0)
        diagonals.append(diagonal)
        norms.append(norm*scale**(2*j))
        if j:
            assert off_square > 0
            squares.append(off_square)
        updated = (x-diagonal)*polynomial-off_square*previous
        previous, polynomial = polynomial, arb_poly([v.mid() for v in updated.coeffs()])
        previous_norm = norm
    next_norm = inner(polynomial, polynomial)*scale**(2*q)
    assert next_norm > 0
    off_diagonals = [b.sqrt() for b in squares]
    seeds = eigh_tridiagonal([float(v) for v in diagonals],
                            [float(v) for v in off_diagonals], eigvals_only=True)

    def poly(t):
        p0, p1, d0, d1 = arb(1), t-diagonals[0], arb(0), arb(1)
        for j in range(1, q):
            p0, p1 = p1, (t-diagonals[j])*p1-squares[j-1]*p0
            d0, d1 = d1, p0+(t-diagonals[j])*d1-squares[j-1]*d0
        return p1, d1

    nodes, centered = [], []
    for seed in seeds:
        t = arb(float(seed))
        for _ in range(6):
            v, dv = poly(t)
            t = (t-v/dv).mid()
        v, dv = poly(t)
        eps = arb(2)**(-ctx.prec+48)+4*abs(v/dv).upper()
        for _ in range(64):
            if poly(t-eps)[0]*poly(t+eps)[0] < 0:
                break
            eps *= 2
        else:
            raise ArithmeticError('Owner Gaussian root not bracketed')
        t = arb(t, eps.upper())
        polynomials = [arb(1)]
        if q > 1:
            polynomials.append((t-diagonals[0])/off_diagonals[0])
        for j in range(1, q-1):
            polynomials.append(((t-diagonals[j])*polynomials[-1]
                                -off_diagonals[j-1]*polynomials[-2])/off_diagonals[j])
        weight = moments[0]/sum(p*p for p in polynomials)
        point = center+scale*t
        assert 0 < point and point < 1 and weight > 0
        nodes.append((point, weight))
        centered.append((t, weight))
    assert all(nodes[j][0] < nodes[j+1][0] for j in range(q-1))
    defects = [abs(sum(w*t**k for t, w in centered)-moments[k]).upper()
               for k in range(2*q)]
    assert max(defects) < arb('1e-60'), 'Owner moment defects too large'
    return nodes, dict(moment_checks=2*q, mass=str(moments[0]),
                       maximum_centered_moment_defect=str(max(defects)),
                       candidate_polynomial_norm=str(next_norm),
                       owner_order=[lo, hi], trials=M,
                       scope='Exact owner moments and positive approximate rule with paid moment defects; '
                             'not an exact Gaussian rule or a full-integrand quadrature bound')


def fourier_error_bound(M, lo, hi, rule, frequency, order=None):
    """Real-axis Taylor remainder plus every measured moment defect.

    With even K, |exp(i*t)-sum_{j<K}(i*t)^j/j!| <= |t|^K/K!.
    Integrate this bound against the exact positive owner measure AND
    the positive computed rule. It does not assume Gaussian exactness.
    """
    K = order or 2*len(rule)
    assert K > 0 and K % 2 == 0
    moments, center, scale = centered_moments(M, lo, hi, K+1)
    nodes = [((x-center)/scale, w) for x, w in rule]
    a = abs(frequency*scale)
    errors, power = arb(0), arb(1)
    for k in range(K):
        observed = sum(w*x**k for x, w in nodes)
        errors += power*abs(observed-moments[k])
        power *= a/(k+1)
    tail = power*(moments[K]+sum(w*x**K for x, w in nodes))
    assert tail > 0
    return errors+tail


def hermite_fourier_bound(M, lo, hi, rule, frequency):
    """Hermite interpolation error, with defects for BOTH interpolation jets.

    For q distinct real nodes, the cosine and sine remainders are each
    bounded by |frequency|^(2q)/(2q)! times the squared nodal polynomial.
    Integrate their Hermite polynomials exactly using the owner moments.
    Nonzero value/derivative moment defects are charged explicitly. Unlike
    the Gaussian remainder formula, this does not assume exact orthogonality.
    """
    q = len(rule)
    moments, center, scale = centered_moments(M, lo, hi, 2*q+1)
    nodes = [((x-center)/scale, w) for x, w in rule]
    polynomial = arb_poly([1])
    for t, _ in nodes:
        polynomial *= arb_poly([-t, 1])

    def integral(p):
        return sum(c*moments[j] for j, c in enumerate(p.coeffs()))

    defects = arb(0)
    omega = abs(frequency*scale)
    for i, (t, weight) in enumerate(nodes):
        # Exact polynomial division by a known root; the remainder is zero.
        reduced, remainder = divmod(polynomial, arb_poly([-t, 1]))
        assert all(v.contains(0) for v in remainder.coeffs())
        denominator, slope = arb(1), arb(0)
        for j, (v, _) in enumerate(nodes):
            if i != j:
                denominator *= t-v
                slope += 1/(t-v)
        squared = (reduced*(1/denominator))**2
        jet = squared*arb_poly([-t, 1])
        value = squared-2*slope*jet
        defects += abs(integral(value)-weight)+omega*abs(integral(jet))
    nodal_norm = integral(polynomial**2)
    assert nodal_norm > 0
    return defects+2*nodal_norm*omega**(2*q)/arb.fac_ui(2*q), defects


def exact_moment_checks():
    """Independent rational polynomial integration, not the beta recurrence."""
    checks = 0
    for M, lo, hi in [(1, 1, 1), (7, 2, 5), (13, 7, 9), (20, 4, 18)]:
        moments = raw_moments(M, lo, hi, 13)
        for k, value in enumerate(moments):
            truth = sum((Fraction(math.comb(M, j)*math.comb(M-j, b)*(-1)**b,
                                  j+k+b)
                         for j in range(lo, hi+1) for b in range(M-j+1)), Fraction(0))
            assert value.contains(fmpq(truth.numerator, truth.denominator)), (M, lo, hi, k)
            checks += 1
    return checks
