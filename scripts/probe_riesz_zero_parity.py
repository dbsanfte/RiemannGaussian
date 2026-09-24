#!/usr/bin/env python3
"""Optional numerical audit of the simple-zero parity cascade.

This is a continuum MODEL, not a theorem or arithmetic prime estimate.
It evaluates all cofactor counts via the Dickman/Buchstab delay equations,
cross-checks a region where at most three counts fit by direct quadrature,
and scans the actual interior share box. No ordinary build invokes it.

The candidate inverse of (1-exp(-J_r))/z^2 on s>d>0 is
  G_r(s,d) = (d/s)*rho(s/r-1)
    + integral_1^(d/r) ((d/r-v)/(s/r-v))*rho(s/r-v-1)*omega(v) dv.
Its analytic identification is NOT currently proved in Lean. Positive
integral recurrences avoid the catastrophic subtraction in forward
integration of rho'(v)=-rho(v-1)/v at large v.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import scipy
from scipy.integrate import quad
from scipy.special import exp1
from scipy.stats import binom

from probe_riesz_parity_packet import rectangle_fraction


class DelayModel:
    def __init__(self, steps, ceiling=42):
        self.steps = steps
        self.grid = np.arange(steps*ceiling+1)/steps
        self.rho = np.zeros_like(self.grid)
        self.rho[:steps+1] = 1
        h = 1/steps
        # v*rho(v)=integral_(v-1)^v rho(t) dt. Re-sum positive terms;
        # a sliding accumulator loses all relative precision in the tail.
        for j in range(steps+1, len(self.grid)):
            self.rho[j] = h*(self.rho[j-steps]/2 +
                            np.sum(self.rho[j-steps+1:j]))/(self.grid[j]-h/2)
        self.omega = np.zeros_like(self.grid)
        self.omega[steps:2*steps+1] = 1/self.grid[steps:2*steps+1]
        integral = 0.
        for j in range(2*steps+1, len(self.grid)):
            integral += h*(self.omega[j-steps-1]+self.omega[j-steps])/2
            self.omega[j] = (1+integral)/self.grid[j]
        self.nodes, self.weights = np.polynomial.legendre.leggauss(48)

    def R(self, v):
        return np.interp(v, self.grid, self.rho, left=1, right=0)

    def W(self, v):
        return np.where(np.asarray(v) < 1, 0,
                        np.interp(v, self.grid, self.omega, left=0, right=1/math.exp(0.5772156649)))

    def G(self, s, d, r):
        assert 0 < d < s and r > 0
        a, b = s/r, d/r
        value = b/a*self.R(a-1)
        cuts = sorted({1., b, *[float(k) for k in range(2, math.ceil(b))],
                       *[a-1-k for k in range(math.ceil(a)) if 1 < a-1-k < b]})
        if b <= 1:
            return float(value)
        for lo, hi in zip(cuts, cuts[1:]):
            v = (lo+hi)/2+(hi-lo)/2*self.nodes
            f = (b-v)/(a-v)*self.R(a-v-1)*self.W(v)
            value += (hi-lo)/2*(self.weights@f)
        return float(value)

    def transform_check(self):
        # This numerical check does not establish transform injectivity.
        rows = []
        for w in (0.5, 1., 2.):
            rhat = np.trapezoid(np.exp(-w*self.grid)*self.rho, self.grid)
            # omega has a unit jump at 1, so integrate starting there.
            what = np.trapezoid(np.exp(-w*self.grid[self.steps:])*
                                self.omega[self.steps:], self.grid[self.steps:])
            rows.append({"w": w, "rho_identity_error": float(w*rhat-math.exp(-exp1(w))),
                         "omega_identity_error": float(1+what-math.exp(exp1(w)))})
        return rows


def hinge(xs, d):
    result = 0.
    for mask in range(1 << len(xs)):
        result += (-1)**mask.bit_count()*max(0., d-sum(x for i,x in enumerate(xs) if mask >> i & 1))
    return result


def direct_small_count(s, d, r):
    assert 2*r < s < 4*r
    pieces = [hinge([s], d)/s]
    pieces.append(-quad(lambda x: hinge([x,s-x], d)/(x*(s-x)), r, s-r,
                        epsabs=1e-11, points=[d,s-d] if r < d < s-r else None)[0]/2)
    if s > 3*r:
        def outer(x):
            end = s-x-r
            if end <= r:
                return 0.
            return quad(lambda y: hinge([x,y,s-x-y], d)/(x*y*(s-x-y)),
                        r, end, epsabs=1e-10)[0]
        pieces.append(quad(outer, r, s-2*r, epsabs=1e-9)[0]/6)
    return pieces


def scan(model):
    uvals = (0.5, 0.500025, 0.50005)
    slopes = (1.95, 1.99, 2., 2.03)
    z, weights = np.polynomial.legendre.leggauss(40)
    ps = 43/80+(9/16-43/80)*(z+1)/2
    rows = []
    for u in uvals:
        for slope in slopes:
            lam = -2*math.log(u)/slope
            low = np.array([model.G(1-p,lam-p,3/250) for p in ps])
            high = np.array([model.G(1-p,lam-p,7/250) for p in ps])
            # The difference selects minimum cofactor share in [3/250,7/250].
            # Cofactor count one cancels identically between the cutoffs.
            integral = (9/16-43/80)/2*(weights@((low-high)/(lam*ps)))
            rows.append({"u":u, "log_n_over_N":slope, "lambda":lam,
                         "support_gap_over_rmax":(1-lam)/(7/250),
                         "max_G_rmax":float(max(high)), "packet_model":float(integral)})
    return rows


def factorial_diagnostics():
    rows = []
    for n in (256,640,1536,4096,16384):
        # This is the exact binomial marginal of one minimal-share leg,
        # not a count or simulation of actual primes.
        bad = binom.cdf(math.ceil(n/200)-1,n+1,3/250)
        # A log-share mask has a boundary layer even with a good order.
        # p=upper selected share: roughly half the factorial mass falls
        # on each side of that SAME boundary, unlike the wider order box.
        at_boundary = binom.cdf(math.floor((n+1)*9/16),n+1,9/16)
        rows.append({"N":n, "minimal_leg_bad_mass":float(bad),
                     "proved_one_leg_envelope":math.exp(-n/400),
                     "upper_share_boundary_lower_fraction":float(at_boundary)})
    return rows


def finite_masked_scan(model):
    """Retain the exact rectangle weight in the continuum minimum-share density.

    Differentiation here is numerical; this is not a proved renewal formula.
    The old allocation is still excluded and explicitly listed as such.
    """
    nodes, weights = np.polynomial.legendre.leggauss(28)
    ps, rs = np.meshgrid(43/80+(9/16-43/80)*(nodes+1)/2,
                        3/250+(7/250-3/250)*(nodes+1)/2,indexing="ij")
    ps, rs = ps.ravel(), rs.ravel()
    measure = (np.outer(weights,weights)*(9/16-43/80)*(7/250-3/250)/4).ravel()
    u=0.50005
    rows=[]
    for n in (256,640,1536,4096):
        total=n/u
        length=-2*n*math.log(u)-2*math.log(n+1)
        lam=length/total
        phase_density=[]
        for p,r in zip(ps,rs):
            eps=r*1e-5
            derivative=(model.G(1-p,lam-p,r+eps)-model.G(1-p,lam-p,r-eps))/(2*eps)
            phase_density.append(-derivative/(lam*p))
        density=np.asarray(phase_density)
        selected=rectangle_fraction(n,ps,rs)*(rs*total > 2*math.log(n))
        rows.append({"N":n,"lambda":lam,"floor_length_error_log_bound":math.log(4*(n+1))+n*math.log(u),
                     "raw_model":float(measure@density),
                     "with_rectangle_and_lower_physical_mask":float(measure@(density*selected)),
                     "maximum_sampled_minimum_share_density":float(max(density)),
                     "warning":"Continuum simple-zero model only; original count-dependent allocation and discrete prime-mask transfer remain outside this computation."})
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--steps", type=int, nargs="+", default=[400,800,1600])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = {"status":"Exploratory continuum parity model; not a certificate or arithmetic bound.",
              "numpy":np.__version__, "scipy":scipy.__version__,
              "input_sha256":{name:hashlib.sha256(Path(__file__).with_name(name).read_bytes()).hexdigest()
                              for name in ("probe_riesz_zero_parity.py","probe_riesz_parity_packet.py")},
              "normalization":"(-1)^(k+1) for k cofactor primes; largest prime supplies the extra minus sign.",
              "mask_warning":"The delay inverse omits finite factorial/allocation masks; only the separate marginal diagnostic retains its exact binomial weights.",
              "levels":[], "factorial_diagnostics":factorial_diagnostics()}
    checks = [(2.5,0.75,1.),(3.5,1.5,1.),(3.5,2.25,1.)]
    for steps in args.steps:
        model = DelayModel(steps)
        crosschecks = []
        for s,d,r in checks:
            pieces=direct_small_count(s,d,r)
            predicted=model.G(s,d,r)
            crosschecks.append({"s":s,"d":d,"r":r,"count_terms":pieces,
                                "direct_sum":sum(pieces),"delay_inverse":predicted,
                                "difference":predicted-sum(pieces)})
        level = {"steps_per_unit":steps,"transform_checks":model.transform_check(),
                 "direct_count_checks":crosschecks,"core_scan":scan(model),
                 "rho_samples":{str(t):float(model.R(t)) for t in (5,9,10,11,15,25,38)}}
        report["levels"].append(level)
        print(json.dumps({"steps":steps,"worst_direct_check":max(abs(x["difference"]) for x in crosschecks),
                          "largest_packet_model":max(abs(x["packet_model"]) for x in level["core_scan"])}),flush=True)
    report["finite_rectangle_model"] = finite_masked_scan(model)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+"\n")


if __name__ == "__main__":
    main()
