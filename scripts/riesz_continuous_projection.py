"""Interval-parameter convolution for the optional continuous Riesz diagnostic.

Keep breakpoint identities affine in the SAME s,d parameters. This avoids
losing exact cell-boundary relations when nodes are balls rather than fixed
rationals. Numerical model only; no prime-sum or outer quadrature theorem.
"""
from dataclasses import dataclass
from fractions import Fraction

from flint import arb, arb_poly
from probe_riesz_continuous_balls import ball, real, weighted_norm


@dataclass(frozen=True)
class Cut:
    s: int = 0
    d: int = 0
    c: Fraction = Fraction(0)

    def __sub__(self, other):
        return Cut(self.s-other.s, self.d-other.d, self.c-other.c)


def compress_model(model, tolerance):
    """Shorten completed numerical density polynomials, paying every removed term.

    Call only after the delay solution has been constructed. This truncates
    numerical Taylor coefficients, NOT prime counts or factorial allocations.
    """
    for row in model.cells:
        for cell in row:
            coefficients = cell.poly.coeffs()
            removed = arb(0)
            while len(coefficients) > 1:
                next_term = abs(coefficients[-1])*model.h**(len(coefficients)-1)
                if not removed+next_term < tolerance:
                    break
                removed += next_term
                coefficients.pop()
            cell.poly = arb_poly(coefficients)
            cell.error = (cell.error+removed).upper()
            cell.norm = weighted_norm(coefficients, model.h)


def response_interval(model, s, d, negligible=None):
    assert 0 < d and d < s
    sq = Fraction(str(s.fmpq())) if s.is_exact() else None
    dq = Fraction(str(d.fmpq())) if d.is_exact() else None

    def canon(c):
        return Cut(c.s if sq is None else 0, c.d if dq is None else 0,
                   c.c+(c.s*sq if sq is not None else 0)+(c.d*dq if dq is not None else 0))

    def ev(c):
        c = canon(c)
        return c.s*s+c.d*d+real(c.c)

    S, gap = canon(Cut(s=1)), canon(Cut(s=1, d=-1))
    if ev(gap) > 1:
        left = gap
    else:
        assert ev(gap) <= 1, 'Unresolved lower-boundary ordering'
        left = Cut(c=Fraction(1))
    right = canon(Cut(s=1, c=Fraction(-1)))
    answer = -d*model.density(0, s)
    if ev(right-left) <= 0:
        return answer
    assert ev(right-left) > 0
    cuts = {canon(left), canon(right)}
    for cell in model.cells[0]:
        for q in (canon(Cut(c=cell.left)), canon(Cut(s=1, c=-cell.left))):
            if q in cuts:
                continue
            if ev(q-left) > 0 and ev(right-q) > 0:
                cuts.add(q)
            else:
                assert ev(q-left) <= 0 or ev(right-q) <= 0, 'Unresolved breakpoint ordering'
    cuts = sorted(cuts, key=lambda c: float(ev(c)))
    segments, envelope = [], abs(answer).upper()
    for a, b in zip(cuts, cuts[1:]):
        midpoint = (ev(a)+ev(b))/2
        ca, cb = model.cell(0, midpoint), model.cell(1, s-midpoint)
        xa, xb = ev(a-Cut(c=ca.left)), ev(S-a-Cut(c=cb.left))
        right_a, right_b = ev(b-Cut(c=ca.left)), ev(S-b-Cut(c=cb.left))
        length = ev(b-a)
        assert length > 0
        assert xa >= 0 and right_a <= model.h
        assert right_b >= 0 and xb <= model.h
        ramp = ev(b-gap)
        envelope += length*ramp*(ca.norm+ca.error)*(cb.norm+cb.error)
        segments.append((a, gap, ca, cb, xa, xb, length, ramp))
    if negligible is not None and negligible(envelope.upper()):
        model.norm_enclosed_points = getattr(model, 'norm_enclosed_points', 0)+1
        return ball(arb(0), envelope)
    integral, error = arb(0), arb(0)
    for a, gap, ca, cb, xa, xb, length, ramp in segments:
        pa = ca.poly(arb_poly([xa, 1]))
        pb = cb.poly(arb_poly([xb, -1]))
        primitive = (pa*pb*arb_poly([ev(a-gap), 1])).integral()
        integral += primitive(length)-primitive(0)
        error += length*ramp*(ca.error*cb.norm+cb.error*ca.norm+ca.error*cb.error)
    return answer-ball(integral, error)


def count_allowance(s, d, first_count=1):
    """Unsigned simplex allowance for model counts k>=first_count.

    Each tilted leg has norm <=7/x<=7 on x>=1. The Riesz difference
    has norm <=2^k*d. The convolution simplex has volume
    (s-k)^(k-1)/(k-1)!, and the symmetric count factor is 1/k!.
    This is used only for numerical exterior/omitted-count budgets.
    """
    import math
    end = math.ceil(float(s.upper()))+1
    assert s < end
    total = arb(0)
    for k in range(max(1, first_count), end):
        if s < k:
            continue
        if s-k >= 0:
            extent = s-k
        else:
            extent = abs(s-k).upper()
        total += arb(14)**k*extent**(k-1)/(arb.fac_ui(k)*arb.fac_ui(k-1))
    return abs(d)*total
