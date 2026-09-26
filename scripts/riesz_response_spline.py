"""Piecewise-polynomial projection of the complete continuous Riesz response.

For fixed gap g=s-d>1 the signed response is
  -(s-g)*a(s) - (((v-g)_+*a(v))*b)(s).
The two renewal densities already carry uniform cell errors. We convolve
their polynomial parts exactly, retain the empty-B term, and separately
bound the propagated cell errors. This is a continuum numerical tool;
no prime transport or outer radial/beta integration is asserted.
"""
from dataclasses import dataclass
from fractions import Fraction

from flint import arb, arb_poly
from probe_riesz_continuous_balls import real


@dataclass(frozen=True)
class Knot:
    gap: int = 0
    offset: Fraction = Fraction(0)

    def __add__(self, other):
        return Knot(self.gap+other.gap, self.offset+other.offset)


@dataclass
class Piece:
    left: arb
    right: arb
    poly: arb_poly  # local coordinate s-left
    error: arb    # uniform error, independent of polynomial roundoff


def convolution_polynomial(a, b):
    """(x_+^i*x_+^j)(s)=i!j!/(i+j+1)! * s_+^(i+j+1)."""
    aa = arb_poly([c*arb.fac_ui(i) for i, c in enumerate(a.coeffs())])
    bb = arb_poly([c*arb.fac_ui(j) for j, c in enumerate(b.coeffs())])
    return arb_poly([0]+[c/arb.fac_ui(k+1) for k, c in enumerate((aa*bb).coeffs())])


class ResponseSpline:
    def __init__(self, model, gap, lo, hi):
        assert 1 < gap < lo < hi
        assert hi < real(model.cells[0][-1].left)+model.h
        self.model, self.gap = model, gap
        self.lo, self.hi = lo, hi
        self.terms = {}

        def ev(k):
            return k.gap*gap+real(k.offset)

        self.ev = ev
        # Represent each polynomial cell sequence by its exact jump in
        # polynomial extension at the left endpoint. No count truncation.
        first = model.cell(0, gap)
        assert real(first.left) <= gap < real(first.left)+model.h
        a = [(Knot(gap=1), first.poly(arb_poly([gap-real(first.left), 1]))
              *arb_poly([0, 1]))]
        previous = None
        b = []
        for cell in model.cells[0]:
            x = real(cell.left)
            if gap < x and x+1 < hi:
                assert previous is not None
                jump = cell.poly-previous.poly(arb_poly([model.h, 1]))
                a.append((Knot(offset=cell.left), jump*arb_poly([x-gap, 1])))
            previous = cell
        previous = None
        for cell in model.cells[1]:
            x = real(cell.left)
            if gap+x >= hi:
                break
            jump = cell.poly if previous is None else (
                cell.poly-previous.poly(arb_poly([model.h, 1])))
            b.append((Knot(offset=cell.left), jump))
            previous = cell
        for ka, pa in a:
            for kb, pb in b:
                k = ka+kb
                if ev(k) < hi:
                    self.terms[k] = self.terms.get(k, arb_poly([]))+convolution_polynomial(pa, pb)

        knots = set(self.terms)
        knots.update(Knot(offset=c.left) for c in model.cells[0])
        points = [(None, lo), (None, hi)]
        for k in knots:
            x = ev(k)
            if lo < x < hi:
                points.append((k, x))
            else:
                assert x <= lo or hi <= x, 'Unresolved spline endpoint'
        points.sort(key=lambda pair: float(pair[1]))
        self.pieces = []
        for (left_knot, left), (_, right) in zip(points, points[1:]):
            assert left < right
            middle = (left+right)/2
            cell = model.cell(0, middle)
            assert real(cell.left) <= left and right <= real(cell.left)+model.h
            poly = -cell.poly(arb_poly([left-real(cell.left), 1]))*arb_poly([left-gap, 1])
            for knot, term in self.terms.items():
                point = ev(knot)
                if point < middle:
                    # The same exact affine knot may be the interval's endpoint.
                    shift = arb(0) if knot == left_knot else left-point
                    poly -= term(arb_poly([shift, 1]))
            error = self.uniform_error(left, right, cell)
            self.pieces.append(Piece(left, right, poly, error))

    def uniform_error(self, left, right, head):
        """Only physical cell norms occur; extended-polynomial norms are unused."""
        m, g = self.model, self.gap
        error = (right-g)*head.error
        for a in m.cells[0]:
            al = max(real(a.left), g.lower())
            ar = min(real(a.left)+m.h, right.upper()-1)
            if ar <= al:
                continue
            for b in m.cells[1]:
                bl = real(b.left)
                low = max(al, left.lower()-(bl+m.h))
                high = min(ar, right.upper()-bl)
                if high <= low:
                    continue
                error += (high-low)*(high-g).upper()*\
                    (a.error*b.norm+b.error*a.norm+a.error*b.error)
        return error.upper()

    def value(self, s):
        for piece in self.pieces:
            if piece.left <= s <= piece.right:
                return piece.poly(s-piece.left)+arb(0, piece.error)
        raise ValueError('Outside spline or unresolved knot')

    def audit(self):
        return dict(pieces=len(self.pieces), convolution_knots=len(self.terms),
                    maximum_degree=max(p.poly.degree() for p in self.pieces),
                    uniform_response_error=str(max(p.error for p in self.pieces)),
                    scope='Complete signed polynomial convolution with density errors; '
                          'no outer quadrature or arithmetic estimate')
