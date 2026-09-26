#!/usr/bin/env python3
"""Optional continuous signed renewal diagnostic with explicit error budgets.

This is a SYNTHETIC finite-mode continuum model, not an arithmetic prime sum
or Lean certificate. It does not integrate the outer radial/owner/beta rules.
It replaces the cutoff lattice at a fixed geometry by a delay equation,
retains both empty atoms, and encloses its inverse ramp convolution.

For sign eps in {-1,1}, f(t)=eps*sum m_i*v_i(t)/t, t>=1, where
v_i(1)=exp(xi_i), v_i'=xi_i*v_i+exp(xi_i)*f(t-1), and f(t)=0 for t<1.
All xi_i have nonpositive real part after a common exact exponential tilt.
On each aligned cell the previous forcing is a polynomial plus a UNIFORM
real-interval error. Propagate that error by variation of constants, using
|exp(xi_i*h)|<=1. Truncate the polynomial-forced solution by its explicit
geometric Taylor tail, then bound the exact division-by-t remainder.
Roundoff is kept separately from propagated error to avoid artificial
exp(|Im xi|*h) amplification of earlier cells' error radii.

Keep outside ordinary CI and the numerical zero-count certificate workflow.
"""
import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import math
from pathlib import Path
import time

from flint import acb, acb_poly, arb, arb_poly, ctx, fmpq, fmpz


def real(q):
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def radius(z):
    return z.real.rad()+z.imag.rad()


def midpoint(z):
    return acb(z.real.mid(), z.imag.mid())


def ball(x, error):
    return x+arb(0, error.upper())


def weighted_norm(coefficients, h):
    total = arb(0)
    for x in reversed(coefficients):
        total = total*h+abs(x)
    return total.upper()


@dataclass
class Cell:
    left: Fraction
    poly: arb_poly
    error: arb
    norm: arb


class ContinuousCascade:
    """Real conjugation-symmetric renewal densities, with uniform cell errors."""
    def __init__(self, nodes, amplitudes, end, subdivision=4, degree=96):
        if subdivision < 1 or subdivision & (subdivision-1):
            raise ValueError('Use a positive power-of-two subdivision')
        assert all(z.real <= 0 for z in nodes)
        assert all(isinstance(m, int) and m >= 0 for m in amplitudes)
        self.hq = Fraction(1, subdivision)
        self.h = real(self.hq)
        self.degree = degree
        self.cells = [[], []]
        # A and B start with the same auxiliary v_i; their density signs differ.
        initial = [z.exp() for z in nodes]
        states = [[midpoint(z) for z in initial] for _ in range(2)]
        errors = [[radius(z).upper() for z in initial] for _ in range(2)]
        exponential = [z.exp() for z in nodes]
        hpower = self.h**(degree+1)
        ratios = [abs(z)*self.h/(degree+2) for z in nodes]
        assert all(r < 1 for r in ratios), 'Taylor degree too small'
        count = math.ceil((Fraction(end)-1)*subdivision)
        for cell_index in range(count):
            left = Fraction(1)+cell_index*self.hq
            c = real(left)
            for channel, sign in enumerate((-1, 1)):
                if cell_index < subdivision:
                    forcing = [arb(0)]*(degree+1)
                    forcing_error = arb(0)
                else:
                    previous = self.cells[channel][cell_index-subdivision]
                    forcing = [previous.poly[j] for j in range(degree+1)]
                    forcing_error = previous.error
                polynomials, uniform_errors = [], []
                for i, xi in enumerate(nodes):
                    coeff = [states[channel][i]]
                    for j in range(degree+1):
                        coeff.append((xi*coeff[-1]+exponential[i]*forcing[j])/(j+1))
                    # For the polynomial forcing, all subsequent Taylor ratios
                    # are xi/(j+1), so this bounds its entire omitted series.
                    tail = abs(coeff[degree+1])*hpower/(1-ratios[i])
                    rounding = weighted_norm([radius(z) for z in coeff[:degree+1]], self.h)
                    centers = [midpoint(z) for z in coeff[:degree+1]]
                    poly = acb_poly(centers)
                    error = (errors[channel][i]+self.h*abs(exponential[i])*forcing_error
                             + tail+rounding).upper()
                    endpoint = poly(self.h)
                    states[channel][i] = midpoint(endpoint)
                    errors[channel][i] = (error+radius(endpoint)).upper()
                    polynomials.append(centers)
                    uniform_errors.append(error)
                # Divide the numerator polynomial exactly by c+x in Taylor form.
                raw = []
                for j in range(degree+1):
                    numerator = sign*sum(m*polynomials[i][j]
                                         for i, m in enumerate(amplitudes))
                    raw.append((numerator-(raw[-1] if j else 0))/c)
                # Keep real centers. Any imaginary roundoff is paid explicitly;
                # the constructor is used only for a real conjugate-mode family.
                centers = [z.real.mid() for z in raw]
                rounding = weighted_norm([z.real.rad()+abs(z.imag) for z in raw], self.h)
                division_tail = abs(raw[-1])*hpower/c
                error = (sum(m*e for m, e in zip(amplitudes, uniform_errors))/c
                         + division_tail+rounding).upper()
                assert error.is_finite()
                self.cells[channel].append(Cell(left, arb_poly(centers), error,
                                               weighted_norm(centers, self.h)))

    def cell(self, channel, x):
        j = math.floor((float(x)-1)/float(self.h))
        j = min(max(j, 0), len(self.cells[channel])-1)
        return self.cells[channel][j]

    def density(self, channel, x):
        c = self.cell(channel, x)
        dx = x-real(c.left)
        assert dx >= 0 and dx <= self.h
        return ball(c.poly(dx), c.error)

    def response(self, s, d):
        """Inverse ramp on 0<d<s, including B's unit atom.

        R(s,d)=-d*a(s)-int_(max(1,s-d))^(s-1)
                         (v-(s-d))*a(v)*b(s-v) dv.
        The A atom has empty support because d<s. A and B's continuous
        density breakpoints are all included before polynomial integration.
        """
        sq = Fraction(s)
        s = real(sq)
        assert 0 < d and d < s
        gap = s-d
        lo = gap if gap > 1 else arb(1)
        hi = s-1
        answer = -d*self.density(0, s)
        if hi <= lo:
            return answer, {'segments': 0, 'convolution_error': '0'}
        # Retain rational breakpoint identities. Evaluating s-(s-c) as
        # unrelated balls would lose the exact cell-end equality.
        cuts = [(lo, None if gap > 1 else Fraction(1)), (hi, sq-1)]
        rational_cuts = set()
        for c in self.cells[0]:
            rational_cuts.add(c.left)
            rational_cuts.add(sq-c.left)
        for q in rational_cuts:
            v = real(q)
            if lo < v and v < hi:
                cuts.append((v, q))
        cuts.sort(key=lambda cut: float(cut[0]))
        integral, error = arb(0), arb(0)
        for (a, aq), (b, bq) in zip(cuts, cuts[1:]):
            middle = (a+b)/2
            ca, cb = self.cell(0, middle), self.cell(1, s-middle)
            xa = real(aq-ca.left) if aq is not None else a-real(ca.left)
            xb = real(sq-aq-cb.left) if aq is not None else s-a-real(cb.left)
            right_a = real(bq-ca.left) if bq is not None else b-real(ca.left)
            right_b = real(sq-bq-cb.left) if bq is not None else s-b-real(cb.left)
            length = real(bq-aq) if aq is not None and bq is not None else b-a
            assert length > 0
            assert xa >= 0 and right_a <= self.h
            assert right_b >= 0 and xb <= self.h
            # Compose in a local variable, avoiding huge global-coordinate powers.
            pa = ca.poly(arb_poly([xa, 1]))
            pb = cb.poly(arb_poly([xb, -1]))
            product = pa*pb*arb_poly([a-gap, 1])
            primitive = product.integral()
            integral += primitive(length)-primitive(0)
            error += length*(b-gap)*(ca.error*cb.norm+cb.error*ca.norm+ca.error*cb.error)
        return answer-ball(integral, error), {
            'segments': len(cuts)-1, 'convolution_error': str(error),
            'max_density_error': str(max(c.error for row in self.cells for c in row)),
        }


def elementary_checks():
    model = ContinuousCascade([acb(0)], [1], Fraction(4), subdivision=4, degree=72)
    rows = []
    for q in (Fraction(5, 4), Fraction(7, 4), Fraction(9, 4), Fraction(11, 4)):
        x = real(q)
        for channel, sign in enumerate((-1, 1)):
            exact = sign/x if q < 2 else (sign+(x-1).log())/x
            value = model.density(channel, x)
            assert value.overlaps(exact)
            assert value.rad() < arb('1e-30')
            rows.append({'x': str(q), 'sign': sign, 'value': str(value)})
    # Independent count-by-count check where exactly one or two cofactors fit.
    # No delay equation is used for the reference integral; enumerate H_2.
    nodes = [acb(-arb(1)/7), acb(0, arb(1)/3), acb(0, -arb(1)/3)]
    mixed = ContinuousCascade(nodes, [1, 3, 3], Fraction(3), subdivision=8, degree=96)
    s, d = arb(5)/2, arb(7)/5
    g = lambda x: sum(m*(xi*x).exp() for m, xi in zip((1, 3, 3), nodes))
    reference = d*g(s)/s
    for lo, hi, constant, slope in ((arb(1), arb(11)/10, 0, 1),
                                    (arb(11)/10, arb(7)/5, arb(11)/10, 0),
                                    (arb(7)/5, arb(3)/2, s, -1)):
        integral = acb.integral(
            lambda x, analytic: g(x)*g(s-x)*(constant+slope*x)/(x*(s-x)),
            lo, hi, abs_tol=arb('1e-60'), rel_tol=arb('1e-60'))
        assert integral.is_finite()
        reference -= integral/2
    answer, _ = mixed.response(Fraction(5, 2), d)
    assert reference.imag.contains(0) and reference.real.overlaps(answer)
    assert reference.real.rad() < arb('1e-50') and answer.rad() < arb('1e-50')
    rows.append({'s': '5/2', 'd': '7/5', 'count_cap': 2,
                 'independent_subset_integral': str(reference.real),
                 'renewal_response': str(answer), 'overlap': True})
    return rows


def run(n, share, subdivision, degree, bits, grids=(), max_radius='1e-35'):
    ctx.prec = bits
    start = time.monotonic()
    u = arb(10001)/20000
    T = (n+1)/u
    p = Fraction(11, 20)
    r = Fraction(share)
    assert 0 < r < Fraction(1, 10)
    s = (1-p)/r
    X = (fmpz(20000)**n)//((fmpz(10001)**n)*(n+1))+2
    L = 2*arb(X).log()
    d = (L/T-real(p))/real(r)
    scale = T*real(r)
    nodes = [acb(-scale/40000), acb(0, 3*scale/500), acb(0, -3*scale/500)]
    model = ContinuousCascade(nodes, [1, 3, 3], s+1, subdivision, degree)
    tilted, audit = model.response(s, d)
    growth = (T*real(1-p)/40000).exp()
    response = tilted*growth
    head = d/real(s)*(1+6*growth*(3*T*real(1-p)/500).cos())
    assert response.is_finite() and response.rad() < arb(max_radius), 'Response enclosure too wide'
    lattice = []
    if grids:
        from probe_riesz_joined_balls import tables
        for ell in grids:
            index = s*ell
            base = math.floor(index)
            fraction = index-base
            stencil = []
            for j in range(-5, 7):
                weight = Fraction(1)
                for k in range(-5, 7):
                    if k != j:
                        weight *= (fraction-k)/(j-k)
                stencil.append((base+j, real(weight)))
            assert sum(w for j, w in stencil).contains(1)
            vals, heads, _ = tables(T, real(r), ell, base+7, L)
            approximation = sum(w*vals[j] for j, w in stencil)*growth
            split = sum(w*(vals[j]-heads[j]) for j, w in stencil)*growth+head
            head_error = head-sum(w*heads[j] for j, w in stencil)*growth
            assert (split-approximation).overlaps(head_error)
            lattice.append({'cutoff_grid': ell, 'finite_lattice_value': str(approximation),
                            'difference_from_continuous': str(approximation-response),
                            'head_split_value': str(split),
                            'head_split_difference_from_continuous': str(split-response),
                            'exact_difference_of_interpolation_methods': str(head_error)})
    return {'N': n, 'owner_share': str(p), 'least_share': str(r),
            'T': '(N+1)/(10001/20000)', 'L': '2*log(floor(u^(-N)/(N+1))+2)',
            'subdivision': subdivision, 'degree': degree, 'bits': bits,
            'response_enclosure': str(response), 'head_removed_enclosure': str(response-head),
            'tilted_response_enclosure': str(tilted), 'propagation': audit,
            'maximum_total_count_at_this_geometry': math.floor(s)+1,
            'lattice_comparisons': lattice,
            'seconds': time.monotonic()-start}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--order', type=int, default=65536)
    parser.add_argument('--shares', nargs='+', default=['1/100', '1/25'])
    parser.add_argument('--subdivision', type=int, default=4)
    parser.add_argument('--degree', type=int, default=128)
    parser.add_argument('--bits', type=int, default=768)
    parser.add_argument('--grids', type=int, nargs='*', default=[])
    parser.add_argument('--max-radius', default='1e-35')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if (args.order < 10000 or args.degree < 32 or args.bits < 256
            or any(g < 4 or g % 4 for g in args.grids) or not 0 < arb(args.max_radius) < 1):
        parser.error('require N>=10000, degree>=32, bits>=256, grids divisible by 4, '
                     '0<max-radius<1')
    ctx.prec = args.bits
    checked = elementary_checks()
    rows = []
    frozen = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    lattice_source = Path(__file__).with_name('probe_riesz_joined_balls.py')
    lattice_hash = hashlib.sha256(lattice_source.read_bytes()).hexdigest()
    for share in args.shares:
        row = run(args.order, share, args.subdivision, args.degree, args.bits,
                  args.grids, args.max_radius)
        rows.append(row)
        print(json.dumps(row), flush=True)
    assert hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == frozen
    assert hashlib.sha256(lattice_source.read_bytes()).hexdigest() == lattice_hash
    out = {'scope': 'Continuous finite-mode fixed-geometry model with stated Taylor and '
                    'propagation budgets; not a Lean certificate, outer coupled integral, '
                    'literal prime sum, or asymptotic claim.',
           'modes': ['0', '1/40000+(3/500)i', '1/40000-(3/500)i'],
           'multiplicities': [1, 3, 3], 'counts': 'All continuum counts; no literal count-mask transfer',
           'empty_atoms': 'Both retained; B atom explicit, A atom zero by d<s',
           'elementary_regressions': checked, 'rows': rows,
           'source_sha256': frozen, 'lattice_probe_sha256': lattice_hash,
           'python_flint': importlib.metadata.version('python-flint')}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')


if __name__ == '__main__':
    main()
