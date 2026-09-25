#!/usr/bin/env python3
"""Optional shifted-center rate audit; no arithmetic packet certificate.

The exact count exponential and two/three-mode algebra are checked
numerically. The jump calculation bounds the compensated supported process,
not an identified multimode inverse. Binomial probabilities are evaluated
exactly in logarithmic form; the Poisson approximation is not used for them.
"""
import argparse
import cmath
import hashlib
import json
import math
from pathlib import Path

import scipy
from scipy.optimize import minimize_scalar
from scipy.special import expi

U = 10001 / 20000
B = 16
GAP = 7 / 25
EULER_GAMMA = 0.5772156649015328606


def count_test(modes):
    w, z = 2.0 + 0.7j, 1.3
    intensities = [cmath.log(w + z - xi) - cmath.log(w - xi) for xi in modes]
    total = sum(intensities)
    # Recursive exponential terms avoid factorial overflow.
    atom, series = 1 + 0j, 0j
    for k in range(1, 301):
        atom *= -total / k
        series -= atom / z**2
    product = math.prod([(w-xi)/(w+z-xi) for xi in modes])
    exact = (1-product)/z**2
    den = [w+z-xi for xi in modes]
    expanded = sum(1/(z*a) for a in den)
    expanded -= sum(1/(den[i]*den[j]) for i in range(len(den)) for j in range(i+1,len(den)))
    if len(den) == 3:
        expanded += z / math.prod(den)
    assert abs(series-exact) < 1e-13
    assert abs(expanded-exact) < 1e-13
    return {"modes": [[v.real,v.imag] for v in modes],
            "count_error": abs(series-exact), "expanded_error": abs(expanded-exact),
            "boundary": "Two modes retain a diagonal delta channel; three retain a delta derivative. No below-diagonal inverse is inferred from this test alone."}


def rate_row(n):
    share = (20*B/39)*math.log1p(n)/n
    def exponent(b):
        return expi(b)-EULER_GAMMA-math.log(b)-b*GAP/share
    opt = minimize_scalar(exponent, bounds=(1e-7,30), method="bounded")
    x = B*math.log1p(n)/(2.03*n)
    log_zero = n*math.log1p(-x)
    log_bad = log_zero+math.log1p(n*x/(1-x))
    source = n*math.log(2*U)
    return {"N": n, "moving_share_bound": share, "optimal_tilt_share": float(opt.x),
            "log_supported_tail_envelope": float(opt.fun),
            "log_source_times_tail_envelope": float(opt.fun+source),
            "minimum_mean_order": n*x,
            "log_binomial_order_lt_two": log_bad,
            "log_source_times_bad_marginal": source+log_bad,
            "log_source_times_relative_product_envelope_leading_term": source+math.log(3)-14*math.log1p(n)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = {"status": "Exploration and rate audit only; no literal packet, zero-free, or RH certificate.",
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "scipy": scipy.__version__, "parameters": {"u": U, "B": B, "gap": GAP},
              "count_tests": [count_test([.1+.3j,.2-.4j]), count_test([.1+.3j,.2-.4j,-.1+.8j])],
              "rates": [rate_row(n) for n in (256,640,1536,4096,8192,100000,1000000,10000000)],
              "interpretation": [
                  "The supported compensated jump tail has an exponential margin; Lean proves a conservative exp(-N/100) bound in its rescaled coordinate.",
                  "The summed bad-order marginal and arithmetic multiplier envelope are only polynomially small. Source growth eventually wins over those absolute envelopes.",
                  "This does not prove divergence of a signed arithmetic packet. A coupled signed error estimate is still needed."]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"report": str(args.output), "count_tests": "passed", "last_rate": report["rates"][-1]}, indent=2))


if __name__ == "__main__":
    main()
