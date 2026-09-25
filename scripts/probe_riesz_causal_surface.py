#!/usr/bin/env python3
"""Optional full radial regression after the causal pole-surface split.

The floor in the moving Riesz length is evaluated with exact integer
arithmetic for the two rational radii. This is a toy inverse, not a prime
packet approximation. The Lean bound retains arbitrary real phase height.
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    mp.mp.dps = 90
    p = mp.mpf(11)/20
    rows = []
    directional_rows = []
    phase_rows = []
    for numerator, denominator in [(1, 2), (10001, 20000)]:
        u = mp.mpf(numerator)/denominator
        for n in [64, 256, 640, 1536, 4096, 8192]:
            cutoff = denominator**n // (numerator**n*(n+1))
            length = 2*mp.log(cutoff+2)
            lo, hi = mp.mpf(39)*n/20, mp.mpf(203)*n/100
            assert length-p*hi > 0

            def gamma_integral(rate):
                return mp.gammainc(n+1, rate*lo, rate*hi)/(rate**(n+1)*mp.factorial(n))

            # exp(L-T) - exp(-(1-p)T) is the complete below-diagonal inverse.
            raw = mp.exp(length)*gamma_integral(mp.mpf(3)/2)-gamma_integral(mp.mpf(3)/2-p)
            assert raw > 0
            log_raw = mp.log10(raw)
            log_normalized = log_raw+(n+1)*mp.log10(u)
            log_bound = (n+1)*mp.log10(mp.mpf(2)/3)
            assert log_normalized < log_bound
            delta = mp.mpf(1)/2-u
            a1 = mp.mpf(1)/2-delta*(1-p)+u
            a2 = mp.mpf(1)/2+(u-delta)*(1-p)
            source_raw = mp.exp(u*length)*gamma_integral(a1)-gamma_integral(a2)
            source_log = mp.log10(source_raw)+(n+1)*mp.log10(u)
            source_bound = (n+1)*mp.log10(mp.mpf(4)/5)
            assert source_log < source_bound
            rows.append({
                "u": f"{numerator}/{denominator}", "N": n,
                "L_over_N": mp.nstr(length/n, 25),
                "minimum_gap_share": mp.nstr(1-length/lo, 25),
                "log10_raw_response": mp.nstr(log_raw, 25),
                "log10_source_normalized_response": mp.nstr(log_normalized, 25),
                "log10_lean_upper_bound": mp.nstr(log_bound, 25),
                "source_matched_log10_raw": mp.nstr(mp.log10(source_raw), 25),
                "source_matched_log10_normalized": mp.nstr(source_log, 25),
                "source_matched_log10_lean_bound": mp.nstr(source_bound, 25),
            })
            if numerator == 10001:
                for label, b in [
                    ("left_half_plane", u/2),
                    ("rotated_minus_1_over_100", -mp.mpf(1)/100+mp.mpf(3)/5*1j),
                    ("rotated_minus_1_over_20", -mp.mpf(1)/20+mp.mpf(3)/5*1j),
                ]:
                    def response():
                        first = mp.exp(b*length)*gamma_integral(mp.mpf(1)/2-delta*(1-p)+b)
                        second = gamma_integral(mp.mpf(1)/2+(b-delta)*(1-p))
                        return first-second
                    raw_mode = response()
                    with mp.workdps(130):
                        raw_check = response()
                        relative = abs(raw_check-raw_mode)/abs(raw_check)
                    assert relative < mp.mpf('1e-60')
                    normalized_log = mp.log(abs(raw_mode))+(n+1)*mp.log(u)
                    # The second, one-sided boundary term dominates for the rotated models.
                    endpoint = mp.mpf(203)/100
                    exponent = (mp.log(u)+1+mp.log(endpoint)-endpoint/2
                                +(delta-b.real)*(1-p)*endpoint)
                    directional_rows.append({
                        "model": label, "N": n, "b": mp.nstr(b, 25),
                        "normalized_leg_pole_radius": mp.nstr(abs(u+b)/u, 25),
                        "log10_source_normalized": mp.nstr(normalized_log/mp.log(10), 25),
                        "log_source_normalized_over_N": mp.nstr(normalized_log/n, 25),
                        "upper_endpoint_second_term_exponent": mp.nstr(exponent, 25),
                        "precision_crosscheck_relative_error": mp.nstr(relative, 8),
                    })
            if numerator == 10001 and n in (256, 1536, 8192):
                b = -mp.mpf(1)/20+mp.mpf(3)/5*1j
                for y in (55, 1000):
                    def phased_response():
                        return (mp.exp(b*length)*gamma_integral(mp.mpf(1)/2-delta*(1-p)+b+1j*y)
                                -gamma_integral(mp.mpf(1)/2+(b-delta)*(1-p)+1j*y))
                    value = phased_response()
                    with mp.workdps(130):
                        check = phased_response()
                        error = abs(value-check)/abs(check)
                    assert error < mp.mpf('1e-60')
                    phase_rows.append({
                        "N": n, "phase_height": y,
                        "b": "-1/20+3i/5",
                        "log10_source_normalized": mp.nstr(mp.log10(abs(value))+(n+1)*mp.log10(u),25),
                        "precision_crosscheck_relative_error": mp.nstr(error,8),
                    })
    # Conditional finite-mode stress test: selected zero and its conjugate,
    # together with BOTH shifted positive copies. These are synthetic input
    # coordinates, not asserted zeros of zeta. The Lean geometry theorem is
    # conditional on an actual NontrivialZetaZero.
    u = mp.mpf(10001)/20000
    beta, height = mp.mpf(3)/2-u, mp.mpf(55)
    center = mp.mpf(3)/2+1j*height
    ratio = center/(center-1)
    zeros = [beta+1j*height, beta-1j*height]
    negative = [zero-1-1j*height for zero in zeros]
    positive = [mp.mpf(1)/2-(center+1-zero)/ratio for zero in zeros]
    pair_rows = []
    for n in [64, 256, 640, 1536, 4096, 8192]:
        length = 2*mp.log(20000**n//(10001**n*(n+1))+2)
        lo, hi = mp.mpf(39)*n/20, mp.mpf(203)*n/100

        def pair_response():
            def gamma_integral(rate):
                return mp.gammainc(n+1,rate*lo,rate*hi)/(rate**(n+1)*mp.factorial(n))
            total = 0
            for j, xi in enumerate(positive):
                other = positive[1-j]
                prefactor = -(xi-negative[0])*(xi-negative[1])/(xi-other)
                # The cutoff-zero residue is exactly -1 for each positive mode.
                total -= gamma_integral(mp.mpf(1)/2-xi*(1-p))
                for i, a in enumerate(negative):
                    z = a-xi
                    residue = prefactor*(a-other)/(z*(a-negative[1-i]))
                    total += residue*mp.exp(z*length)*gamma_integral(mp.mpf(1)/2-xi+p*a)
            return total

        value = pair_response()
        with mp.workdps(130):
            check = pair_response()
            error = abs(value-check)/abs(check)
        assert error < mp.mpf('1e-60')
        log_norm = mp.log10(abs(value))+(n+1)*mp.log10(u)
        pair_rows.append({
            "N": n, "log10_source_normalized": mp.nstr(log_norm,25),
            "log_source_normalized_over_N": mp.nstr(log_norm*mp.log(10)/n,25),
            "precision_crosscheck_relative_error": mp.nstr(error,8),
        })
    report = {
        "status": "Exact-floor toy radial regression; not a literal zeta packet estimate.",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "mpmath": mp.__version__, "precision_decimal_digits": mp.mp.dps,
        "largest_share": "11/20", "phase_height_in_probe": 0,
        "phase_height_in_lean_bound": "arbitrary real y",
        "moving_length": "2*log(floor(u**(-N)/(N+1))+2)",
        "radial_window": "39*N/20 < T <= 203*N/100",
        "kernel": "exp(L_N-T)-exp(-(1-p)*T)",
        "rows": rows,
        "directional_rows": directional_rows,
        "phase_rows": phase_rows,
        "shifted_conjugate_pair": {
            "scope": "Finite rational model with synthetic beta=19999/20000 and gamma=55; not a claimed actual zero or full zeta inverse.",
            "count_factor": "prod_a((w-a)/(w+z-a))*prod_xi((w+z-xi)/(w-xi))",
            "negative_modes": [mp.nstr(a,25) for a in negative],
            "positive_shifted_modes": [mp.nstr(a,25) for a in positive],
            "normalized_shifted_pole_moduli": [mp.nstr(abs((mp.mpf(1)/2-a)/u),25) for a in positive],
            "rows": pair_rows,
        },
        "source_matched_kernel": "exp((1/2-u)*(1-p)*T)*(exp(u*(L_N-T))-exp(-u*(1-p)*T))",
        "source_matched_normalized_count_factor": "(1-t/2)/(1-t), exactly at w=1/2,z=-u*t",
        "rotated_models": "Exact complex-mode inverse models; not actual zeta remainders. Growth is numerical here.",
        "interpretation": [
            "The persistent fixed-slice Taylor tail is not a source-scale lower bound for this radial inverse.",
            "A cutoff-only causal multiplier matches the entire selected pole surface exactly.",
            "The remaining kernel has a physical-gap exponential saving; the full radial integral decays.",
            "The unscaled comparison has Lean bound (2/3)**(N+1); the source-matched regression has bound (4/5)**(N+1).",
            "The rotated analytic poles show that the Cauchy radius alone does not predict radial suppression.",
            "A joint kernel envelope M*exp(-7*T/25000) is sufficient for the compiled bound M*(9999/10000)**(N+1).",
            "A corresponding causal factorization and strict-core estimate for the actual zeta remainder remain open.",
        ],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"report": str(args.output), "last_row": rows[-1]}, indent=2))


if __name__ == "__main__":
    main()
