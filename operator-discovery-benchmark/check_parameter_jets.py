#!/usr/bin/env python3
"""Independent polynomial, native-series and Cauchy checks of parameter jets."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from math import factorial
from pathlib import Path
import random
import flint

BASE = Path(__file__).resolve().parent


def read(path):
    return json.loads(Path(path).read_text())


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def digest(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(",", ":"),
                                   allow_nan=False).encode()).hexdigest()


def real(x):
    x = Q(x)
    return flint.arb(x.numerator)/x.denominator


def multiply(a, b, order):
    return [sum((a[k]*b[j-k] for k in range(j+1)), Q(0)) for j in range(order+1)]


def direct_binomial_jets(f, centre, order):
    """Different route: expand the finite binomial polynomials in the centre."""
    N = len(f)-1
    h = list(f)
    h[1] -= 1
    power = [Q(0)]*(N+1)
    power[1] = 1
    polynomial = [Q(1)] + [Q(0)]*order
    out = [[Q(0)]*(N+1) for _ in range(order+1)]
    for k in range(N.bit_length()):
        for j in range(order+1):
            for n in range(1, N+1):
                out[j][n] += polynomial[j]*power[n]
        polynomial = multiply(polynomial, [Q(centre-k, k+1), Q(1, k+1)] + [Q(0)]*(order-1), order)
        power = [Q(0)] + [sum((power[d]*h[n//d] for d in range(1, n+1) if n%d==0), Q(0))
                          for n in range(1, N+1)]
    return out


def sieve(N):
    spf = list(range(N+1))
    for p in range(2, N+1):
        if spf[p] == p:
            for n in range(p*p, N+1, p):
                if spf[n] == n:
                    spf[n] = p
    return spf


def prime_polynomial_jets(centre, N, order, spf):
    f = [[Q(0)]*(N+1) for _ in range(order+1)]
    f[0][1] = 1
    for n in range(2, N+1):
        p, r, exponent = spf[n], n, 0
        local = [Q(1)]+[Q(0)]*order
        while r%p == 0:
            r //= p
            exponent += 1
            local = multiply(local, [Q(exponent-1-centre, exponent), Q(-1, exponent)] + [Q(0)]*(order-1), order)
        product = multiply([row[r] for row in f], local, order)
        for j in range(order+1):
            f[j][n] = product[j]
    return f


def native_kernel_jet(u, order, kappa, terms=240):
    """Native power-series arithmetic and reciprocal Gamma, not log-Gamma jets."""
    a = flint.arb_series([0, 1], prec=order+1)
    polynomial = flint.arb_series([1], prec=order+1)
    z, term = real(kappa)*u, flint.arb(1)
    for k in range(1, terms+1):
        term *= z/k
        polynomial += a/(a+k)*term
    result = ((a*u.log()).exp()*(a+1).rgamma())*polynomial
    # Each Taylor coefficient of the omitted hypergeometric sum has the
    # explicit absolute tail. Propagate those balls by native series products.
    magnitude = abs(z).upper()
    assert magnitude/(terms+2) < 1
    remainder = [flint.arb(0)]
    for j in range(1, order+1):
        radius = (magnitude**(terms+1)/factorial(terms+1)/(terms+1)**j /
                  (1-magnitude/(terms+2))).upper()
        remainder.append(flint.arb(0, radius))
    result += ((a*u.log()).exp()*(a+1).rgamma())*flint.arb_series(remainder, prec=order+1)
    return [result[j] for j in range(order+1)]


def cauchy_kernel_coefficient(u, kappa, j):
    r = real(Q(1, 4))
    corners = [flint.acb(r,r), flint.acb(-r,r), flint.acb(-r,-r), flint.acb(r,-r)]
    def integrand(a, analytic):
        return (a*u.log()).exp()*(1+a).rgamma()*flint.acb(real(kappa)*u).hypgeom_1f1(a,1+a)/a**(j+1)
    value = sum((flint.acb.integral(integrand, corners[k], corners[(k+1)%4],
                 abs_tol=real(Q(1,2**100)), rel_tol=real(Q(1,2**100)),
                 eval_limit=30000, depth_limit=28) for k in range(4)), flint.acb(0))
    value /= 2*flint.arb.pi()*flint.acb(0,1)
    assert value.is_finite() and value.imag.contains(0) and value.real.rad()<real(Q(1,2**80))
    return value.real


def enclosure(stored, value):
    ball = flint.arb(stored)
    assert ball.is_finite() and value.is_finite() and ball.contains(value)
    assert ball.rad()<real(Q(1,10**35))*(1+abs(value))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", type=Path, required=True)
    directory = parser.parse_args().run_dir.resolve()
    spec, cases, data = (read(directory/n) for n in ("protocol.json", "cases.json", "jet_data.json"))
    for name, expected in spec["code_sha256"].items():
        assert sha(BASE/name) == expected
    source = Path(spec["source_run"])
    assert sha(source/"verification.json") == spec["source_verification_sha256"]
    assert read(source/"verification.json")["all_passed"]
    assert data["protocol_sha256"] == cases["protocol_sha256"] == digest(spec)
    assert data["cases_sha256"] == digest(cases) and cases["created_after_protocol_frozen"]
    assert spec["scope"] == "guided_calibration_no_independent_discovery_claim"
    assert data["scope"] == "guided_parameter_jet_and_prime_recovery_calibration"
    assert not spec["producer_prime_or_factor_oracle"] and spec["no_finite_to_uniform_promotion"]
    assert not data["new_prime_distribution_bound_proved"] and not data["RH_proved"]
    assert not data["uniform_RH_sufficient_signed_controls_verified"]
    assert not data["coupled_RH_sufficient_target"]["uniform_premise_proved"]
    order, N = spec["jet_order"], spec["cutoff"]
    rng = random.Random(int(cases["seed"]))
    points = sorted(set(map(Q, spec["boundary_points"])) |
                    {Q(rng.randint(17,2*N-1),2) for _ in range(4)})
    assert cases["points"] == list(map(str,points))
    assert set(data["coefficient_jets"]) == set(spec["coefficient_centres"])
    assert len(data["generic_jets"]) == spec["generic_inputs"]
    assert [(v["u"],v["kappa"]) for v in data["kernel_jets"]] == [
        (u,k) for u in spec["kernel_u"] for k in spec["kernel_shifts"]]
    assert [(v["x"],v["coefficient_slope"],v["kernel_slope"]) for v in data["family_jets"]] == [
        (str(x),q,r) for x in points for q,r in spec["path_slopes"]]
    assert [v["x"] for v in data["decoded_counts"]] == list(map(str,points))
    assert [(v["a"],v["x"]) for v in data["finite_difference_probes"]] == [
        (str(Q(1,d)),str(x)) for d in spec["probe_denominators"] for x in points]
    flint.ctx.prec, flint.ctx.cap = 640, order+1
    spf = sieve(N)
    exact = 0
    for record in data["generic_jets"]:
        f = [Q(0),Q(1)] + [Q(rng.randint(-3,3),rng.randint(1,4)) for _ in range(spec["generic_cutoff"]-1)]
        a = Q(rng.randint(-3,3),rng.randint(1,4))
        assert record["input"] == list(map(str,f)) and Q(record["centre"]) == a
        observed = direct_binomial_jets(f,a,order)
        assert record["jets"] == [[str(v) for v in row] for row in observed]
        exact += (len(f)-1)*(order+1)
    by_centre = {}
    for a in map(Q,spec["coefficient_centres"]):
        by_centre[a] = prime_polynomial_jets(a,N,order,spf)
        assert data["coefficient_jets"][str(a)] == [[str(v) for v in row] for row in by_centre[a]]
        exact += N*(order+1)
    d, lam = by_centre[Q(0)][1], [Q(0)]*(N+1)
    for n in range(2,N+1):
        p,r,k = spf[n],n,0
        while r%p == 0:
            r //= p
            k += 1
        lam[n] = Q(1,k) if r==1 else Q(0)
        assert d[n] == -lam[n]
    native_count, cauchy_count = 0,0
    for record in data["kernel_jets"]:
        u,kappa = map(Q,(record["u"],record["kappa"]))
        observed = native_kernel_jet(real(u),order,kappa)
        for j,v in enumerate(observed):
            enclosure(record["jets"][j],v)
            native_count += 1
            cauchy = cauchy_kernel_coefficient(real(u),kappa,j)
            assert cauchy.contains(v)
            cauchy_count += 1
        if kappa==1:
            assert observed[1].overlaps(real(u).ei())
    complete = 0
    coefficient_jets = by_centre[Q(0)]
    for record in data["family_jets"]:
        x,q,r = map(Q,(record["x"],record["coefficient_slope"],record["kernel_slope"]))
        observed = [flint.arb(0) for _ in range(order+1)]
        for n in range(1,N+1):
            if n>=x or not any(row[n] for row in coefficient_jets):
                continue
            weights = native_kernel_jet(real(x/n).log(),order,1)
            for j in range(order+1):
                observed[j] += sum((real(coefficient_jets[k][n]*q**k*r**(j-k))*weights[j-k]
                                    for k in range(j+1)), flint.arb(0))
        for j,v in enumerate(observed):
            enclosure(record["jets"][j],v)
            complete += 1
        prime_power_count = sum((lam[n] for n in range(2,N+1) if n<x),Q(0))
        target = real(r)*real(x).log().ei()-real(q*prime_power_count)
        assert observed[0].contains(1) and observed[1].overlaps(target)
    for record in data["decoded_counts"]:
        x = Q(record["x"])
        count = sum((lam[n] for n in range(2,N+1) if n<x),Q(0))
        pi = sum(1 for p in range(2,N+1) if p<x and spf[p]==p)
        assert Q(record["prime_power_count_strict"]) == count
        assert Q(record["prime_count_strict"]) == pi
    quotient_count = 0
    errors = {}
    for record in data["finite_difference_probes"]:
        a,x = map(Q,(record["a"],record["x"]))
        f = prime_polynomial_jets(a,N,0,spf)[0]
        value = flint.arb(0)
        for n in range(1,N+1):
            if n>=x:
                continue
            u = real(x/n).log()
            incomplete = flint.acb(-u).gamma_lower(real(a),regularized=2)
            assert incomplete.is_finite() and incomplete.imag.contains(0)
            value += real(f[n])*u**real(a)*incomplete.real
        quotient = (value-1)/real(a)
        enclosure(record["value"],value)
        enclosure(record["difference_quotient"],quotient)
        target = real(x).log().ei()-real(sum((lam[n] for n in range(2,N+1) if n<x),Q(0)))
        errors.setdefault(str(x),{})[str(a)] = float(abs(quotient-target).upper())
        quotient_count += 1
    last,first = (str(Q(1,d)) for d in (spec["probe_denominators"][-1],spec["probe_denominators"][0]))
    convergence = sum(v[last]<v[first] for v in errors.values())
    checks = {"frozen_sources_and_explicit_guided_scope_checked": True,
        "general_rational_inputs_checked_by_independent_binomial_polynomials": True,
        "actual_arithmetic_jets_checked_by_prime_factor_polynomials": True,
        "kernel_jets_checked_by_native_series_and_rigorous_Cauchy_contours": True,
        "complete_parameter_family_jets_and_strict_endpoints_checked": True,
        "exact_prime_power_and_root_decoded_prime_counts_checked": True,
        "finite_difference_values_checked_by_incomplete_gamma": True,
        "unproved_coupled_global_premise_and_RH_status_preserved": True}
    result = {"all_passed": all(checks.values()),"checks":checks,
              "protocol_sha256":digest(spec),"jet_data_sha256":sha(directory/"jet_data.json"),
              "checker_sha256":sha(BASE/"check_parameter_jets.py"),
              "exact_coefficient_values_checked":exact,"native_kernel_jet_values":native_count,
              "rigorous_Cauchy_kernel_coefficients":cauchy_count,
              "complete_family_jet_values_checked":complete,"decoded_prime_cases":len(points),
              "complete_difference_quotient_cases":quotient_count,
              "observed_convergence_cases":convergence,"observed_convergence_total":len(errors),
              "observed_difference_quotient_errors":errors,
              "uniform_RH_sufficient_signed_controls_verified":[],"RH_proved":False}
    (directory/"verification.json").write_text(json.dumps(result,indent=2,allow_nan=False)+"\n")
    print("Independent parameter-jet calibration",sum(checks.values()),"/",len(checks),flush=True)


if __name__ == "__main__":
    main()
