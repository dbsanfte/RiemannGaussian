#!/usr/bin/env python3
"""Optional density diagnostic for all in-core extensions of a model triple.

This is NOT a literal prime sum or a certified quadrature. The base logs
are all 2N/3. The inserted-prime measure is replaced by dp/log(p), and the
old allocation and other masks are omitted. The exact factorial ratio and
moving length remain. The separate Lean theorem uses actual Chebyshev
bounds, not this density replacement. Run outside ordinary CI.
"""
import hashlib
import json
import math
from pathlib import Path

from scipy.integrate import quad

from probe_riesz_joint_core import length


def row(N):
    T, L = 2.0*N, length(N)
    assert 1.37*N <= L <= 1.4*N
    assert 4*N/3 + .03*N <= L

    def integrand(v):
        # Prime density cancels the log(a) in the extension coefficient.
        # This unproved replacement is the sole purpose of the diagnostic.
        return ((T+v)/(T*(T-L))
                * math.exp(N*math.log1p(v/T)-v/2))

    mass, error = quad(integrand, 0.0, .03*N, epsabs=1e-12, epsrel=1e-11)
    return dict(N=N, moving_length=L, relative_density_mass=mass,
                scaled_by_sqrt_N=math.sqrt(N)*mass,
                quadrature_error_estimate_not_certified=error)


def main():
    rows = [row(N) for N in (1024, 4096, 16384, 65536)]
    payload = dict(
        scope="uncertified prime-density model with equal base logarithms",
        rows=rows,
        limitations=[
            "The base is a log-share model, not three actual prime labels.",
            "The inserted-prime density replacement is unproved.",
            "Allocation and additional literal masks are omitted.",
            "No roundoff enclosure or cofinal conclusion from samples.",
            "A relative component bound is not an absolute source allowance.",
            "The whole signed core complement remains unpaid."],
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out = Path(__file__).resolve().parents[1]/"docs/riesz-core-extensions-probe.json"
    out.write_text(json.dumps(payload, indent=2)+"\n")
    for entry in rows:
        print(entry, flush=True)


if __name__ == "__main__":
    main()
