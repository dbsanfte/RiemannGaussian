#!/usr/bin/env python3
"""Charged raw-kernel rescue through N-1 and labeled quadratic carries.

The public routines receive N, a literal base and an optional public width.
One additive prefix polynomial is retained at N-1 and reused at every
residual divisor. Exact order extraction either succeeds, exposes a proper
factor, or reports its unresolved rough part. No factorization or primality
oracle occurs inside those routines. This remains an optional research
replay, not a universal sixth-root factorizer or a backend bit certificate.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import runpy
import time

ROOT = Path(__file__).resolve().parents[1]
STAGED = runpy.run_path(str(ROOT/"scripts/probe_semiprime_staged_seed.py"))
PREFIX = STAGED["PREFIX"]
PARENT = "docs/semiprime-staged-seed-audit.json"
SEED = 202610030603


def trial_factors(value, metrics):
    """Used only at value<=B^2, hence at most B trial divisors."""
    factors, divisor = {}, 2
    while divisor*divisor <= value:
        metrics["trial_divisor_tests"] += 1
        if value % divisor == 0:
            exponent = 0
            while value % divisor == 0:
                metrics["trial_strip_divisions"] += 1
                value //= divisor
                exponent += 1
            factors[divisor] = exponent
        divisor += 1
    if value > 1:
        factors[value] = factors.get(value, 0)+1
    return factors


def known_order_factors(exponent, width):
    """Public partial factorization; reuse one source modulo each divisor.

    Clearing the B^2 prefix and reaching R<=B^4 proves primality, as in
    rough_residual_prime_after_prefix. A larger rough R stays unresolved.
    """
    if exponent < 1 or width < 1:
        raise ValueError("positive exponent and width required")
    start = time.perf_counter()
    remaining, known, rounds = exponent, {}, []
    metrics = dict(polynomial_sources=0, root_residues=0, target_residues=0,
                   polynomial_coefficients=0, residual_column_gcds=0,
                   lazy_leaf_gcds=0, retained_value_reductions=0,
                   trial_divisor_tests=0, trial_strip_divisions=0,
                   residual_strip_tests=0, residual_strip_divisions=0,
                   geometric_rows=0)
    values = []
    if exponent > width*width:
        batch = PREFIX["MonicBatch"](exponent)
        polynomial = batch.tree([(-(i+1)) % exponent for i in range(width)])[0]
        values = batch.evaluate(polynomial, [j*width for j in range(width)])
        metrics.update(polynomial_sources=1, root_residues=width,
                       target_residues=width, polynomial_coefficients=len(polynomial),
                       **batch.stats())
    while remaining > 1:
        if remaining <= width*width:
            tail = trial_factors(remaining, metrics)
            for prime, power in tail.items():
                known[prime] = known.get(prime, 0)+power
            rounds.append(dict(residual=remaining, status="small-trial-tail", factors=tail))
            remaining = 1
            break
        for column, value in enumerate(values):
            metrics["retained_value_reductions"] += 1
            reduced = value % remaining
            metrics["residual_column_gcds"] += 1
            hit = math.gcd(remaining, reduced)
            if hit != 1:
                break
        else:
            certified = remaining <= width**4
            rounds.append(dict(residual=remaining,
                               status="rough-prime-certified" if certified else "rough-unresolved",
                               checked_columns=len(values), fourth_power_bound=width**4))
            if certified:
                known[remaining] = 1
                remaining = 1
            break
        # A nonunit block contains a small leaf even if its column GCD is
        # the entire current modulus. Only that block is expanded.
        for offset in range(width):
            leaf = column*width+offset+1
            metrics["lazy_leaf_gcds"] += 1
            divisor = math.gcd(remaining, leaf)
            if divisor > 1:
                break
        else:
            raise AssertionError("retained nonunit column has no nonunit leaf")
        assert divisor <= width*width and remaining % divisor == 0
        small_factors = trial_factors(divisor, metrics)
        old_remaining, stripped = remaining, {}
        for prime in small_factors:
            power = 0
            while True:
                metrics["residual_strip_tests"] += 1
                if remaining % prime:
                    break
                metrics["residual_strip_divisions"] += 1
                remaining //= prime
                power += 1
            known[prime] = known.get(prime, 0)+power
            stripped[prime] = power
        assert remaining < old_remaining and exponent % remaining == 0
        rounds.append(dict(residual=old_remaining, status="small-primes-stripped",
                           column=column, leaf=leaf, divisor=divisor,
                           factors=stripped, next_residual=remaining))
    assert math.prod(prime**power for prime, power in known.items())*remaining == exponent
    return dict(exponent=exponent, width=width, known_factors=known,
                unresolved_residual=remaining, complete=remaining == 1,
                retained_values=values, rounds=rounds, metrics=metrics,
                elapsed_ms=1000*(time.perf_counter()-start))


def wrapped_candidate(n, modulus, label):
    """Literal Nat-subtraction semantics of the Lean reconstruction."""
    quotient = (n-1)//modulus
    index_sum = quotient % modulus+label*modulus
    index_product = max(0, quotient//modulus-label)
    discriminant = max(0, index_sum*index_sum-4*index_product)
    return modulus*(max(0, index_sum-math.isqrt(discriminant))//2)+1


def kernel_rescue(n, base, width=None):
    """No hidden order, prime factor, factorization or primality input."""
    if n < 4:
        raise ValueError("composite-sized input required")
    start = time.perf_counter()
    width = PREFIX["sixth_width"](n) if width is None else width
    if width < 1:
        raise ValueError("positive width required")
    metrics = dict(base_gcds=1, raw_powers=0, order_powers=0, order_gcds=0,
                   order_verification_powers=0, order_verification_gcds=0,
                   candidate_square_roots=0, candidate_gcds=0, geometric_rows=0)
    result = dict(N=n, base=base, width=width, metrics=metrics, factor=None,
                  power_trace=[], candidate_trace=[])

    def finish(status, factor=None):
        if factor is not None:
            assert 1 < factor < n and n % factor == 0
        result.update(status=status, factor=factor,
                      elapsed_ms=1000*(time.perf_counter()-start))
        return result

    unit_gcd = math.gcd(n, base)
    if 1 < unit_gcd < n:
        return finish("base-factor", unit_gcd)
    if unit_gcd != 1:
        return finish("nonunit-base")
    metrics["raw_powers"] += 1
    if pow(base, n-1, n) != 1:
        return finish("outside-raw-kernel")
    setup = known_order_factors(n-1, width)
    result["exponent_setup"] = setup
    exponent = n-1
    for prime in sorted(setup["known_factors"]):
        while exponent % prime == 0:
            metrics["order_powers"] += 1
            power = pow(base, exponent//prime, n)
            metrics["order_gcds"] += 1
            divisor = math.gcd(n, power-1)
            result["power_trace"].append(dict(exponent=exponent, removed_divisor=prime,
                                               value=power, gcd=divisor))
            if 1 < divisor < n:
                result["retained_exponent"] = exponent
                return finish("order-power-factor", divisor)
            if divisor == 1:
                break
            exponent //= prime
    rough = setup["unresolved_residual"]
    if rough > 1:
        # Try to remove the entire unknown part; success need not factor it.
        assert exponent % rough == 0
        metrics["order_powers"] += 1
        power = pow(base, exponent//rough, n)
        metrics["order_gcds"] += 1
        divisor = math.gcd(n, power-1)
        result["power_trace"].append(dict(exponent=exponent, removed_divisor=rough,
                                           value=power, gcd=divisor, rough_whole=True))
        if 1 < divisor < n:
            result["retained_exponent"] = exponent
            return finish("rough-power-factor", divisor)
        if divisor == 1:
            result["retained_exponent"] = exponent
            return finish("unresolved-rough-order")
        exponent //= rough
    # All remaining prime divisors have public certificates. These powers
    # derive the exact order; they do not accept an oracle order as input.
    metrics["order_verification_powers"] += 1
    assert pow(base, exponent, n) == 1
    prime_divisors = [p for p in sorted(setup["known_factors"]) if exponent % p == 0]
    for prime in prime_divisors:
        metrics["order_verification_powers"] += 1
        power = pow(base, exponent//prime, n)
        metrics["order_verification_gcds"] += 1
        divisor = math.gcd(n, power-1)
        assert divisor != n
        if 1 < divisor < n:
            return finish("order-certificate-factor", divisor)
    result.update(certified_order=exponent, order_prime_divisors=prime_divisors,
                  cubic_size_bound=n < exponent**3,
                  wrapped_size_bound=width**3 <= exponent**2)
    for label in range(2*width):
        candidate = wrapped_candidate(n, exponent, label)
        metrics["candidate_square_roots"] += 1
        metrics["candidate_gcds"] += 1
        divisor = math.gcd(n, candidate)
        result["candidate_trace"].append(dict(label=label, candidate=candidate, gcd=divisor))
        if 1 < divisor < n:
            return finish("common-order-factor" if label == 0 else "wrapped-common-order-factor",
                          divisor)
    return finish("unresolved-common-order")


def public_pass(n, scan_cap=None):
    """Try the previous public pipeline, then rescue one recorded kernel."""
    start = time.perf_counter()
    square_root = math.isqrt(n)
    preprocessing = dict(square_root_queries=1, square_gcds=0)
    if square_root*square_root == n:
        preprocessing["square_gcds"] += 1
        divisor = math.gcd(n, square_root)
        if 1 < divisor < n:
            return dict(N=n, width=PREFIX["sixth_width"](n), factor=divisor,
                        status="square-factor", preprocessing_metrics=preprocessing,
                        elapsed_ms=1000*(time.perf_counter()-start))
    previous = STAGED["seeded_source_pass"](n, scan_cap)
    result = dict(N=n, width=previous["width"], factor=previous["factor"],
                  status=previous["status"], staged_pass=previous,
                  preprocessing_metrics=preprocessing)
    if previous["status"] == "no-raw-seed":
        kernels = [entry["base"] for entry in previous["raw_screen"]["screened"]
                   if entry["status"] == "raw-kernel"]
        if kernels:
            rescue = kernel_rescue(n, kernels[0], previous["width"])
            result.update(kernel_rescue=rescue, factor=rescue["factor"], status=rescue["status"])
    result["elapsed_ms"] = 1000*(time.perf_counter()-start)
    return result


def validate():
    # Reference arithmetic is outside charged public routines and timing.
    from sympy import divisors, factorint, n_order, primerange

    retained_comparisons = saturated_reductions = 0
    for original in range(4, 129):
        for width in range(1, math.isqrt(original-1)+1):
            batch = PREFIX["MonicBatch"](original)
            values = batch.evaluate(batch.tree([(-(i+1)) % original
                                                for i in range(width)])[0],
                                    [j*width for j in range(width)])
            for residual in divisors(original):
                expected = [math.prod(j*width+i+1 for i in range(width)) % residual
                            for j in range(width)]
                assert [v % residual for v in values] == expected
                retained_comparisons += 1
                saturated_reductions += sum(v == 0 for v in expected)
    partial_factorizations = certified_primes = unresolved_tails = 0
    for n in range(4, 2049):
        setup = known_order_factors(n-1, PREFIX["sixth_width"](n))
        reference = {int(p): int(e) for p, e in factorint(n-1).items()}
        assert all(reference[p] == e for p, e in setup["known_factors"].items())
        assert setup["metrics"]["polynomial_sources"] <= 1
        certified_primes += sum(r["status"] == "rough-prime-certified" for r in setup["rounds"])
        unresolved_tails += int(not setup["complete"])
        partial_factorizations += 1
    zero_wrap_cases = wrap_bound_cases = square_cases = 0
    primes = list(primerange(3, 150))
    for index, p in enumerate(primes):
        for q in primes[index:]:
            n, width = p*q, PREFIX["sixth_width"](p*q)
            for modulus in divisors(math.gcd(p-1, q-1)):
                actual_label = ((p-1)//modulus+(q-1)//modulus)//modulus
                assert wrapped_candidate(n, modulus, actual_label) == p
                if n < modulus**3:
                    assert actual_label == 0 and wrapped_candidate(n, modulus, 0) == p
                    zero_wrap_cases += 1
                if p > width*width and width**3 <= modulus**2:
                    assert actual_label < 2*width
                    assert any(1 < math.gcd(n, wrapped_candidate(n, modulus, t)) < n
                               for t in range(2*width))
                    wrap_bound_cases += 1
                square_cases += int(p == q)
    controls = [kernel_rescue(1373653, 2), kernel_rescue(1373653, 3),
                kernel_rescue(769841, 508038), kernel_rescue(697, 696),
                kernel_rescue(299, 298), kernel_rescue(13747, 4)]
    assert controls[0]["factor"] == 1657 and controls[0]["status"] == "order-power-factor"
    assert controls[1]["certified_order"] == 207 and controls[1]["factor"] == 829
    wrapped = controls[2]
    assert wrapped["certified_order"] == 40 and wrapped["factor"] == 641
    assert wrapped["status"] == "wrapped-common-order-factor"
    assert not wrapped["cubic_size_bound"] and wrapped["wrapped_size_bound"]
    assert wrapped["candidate_trace"] == [dict(label=0, candidate=121, gcd=1),
                                           dict(label=1, candidate=641, gcd=641)]
    assert controls[3]["certified_order"] == 2 and controls[3]["factor"] is None
    assert controls[3]["status"] == "unresolved-common-order"
    removable = controls[4]
    assert not removable["exponent_setup"]["complete"]
    assert removable["exponent_setup"]["unresolved_residual"] == 149
    assert removable["certified_order"] == 2 and removable["factor"] is None
    assert removable["power_trace"][-1]["rough_whole"]
    assert removable["power_trace"][-1]["gcd"] == 299
    active = controls[5]
    assert active["status"] == "unresolved-rough-order" and active["factor"] is None
    assert active["exponent_setup"]["unresolved_residual"] == 2291
    assert active["retained_exponent"] == 2291
    assert "certified_order" not in active
    # This exact reference is a diagnostic, outside the public routine.
    assert int(n_order(4, 13747)) == 29
    assert wrapped_candidate(13747, 29, 0) == 59
    for control in controls:
        setup = control["exponent_setup"]
        reference = {int(p): int(e) for p, e in factorint(control["N"]-1).items()}
        assert all(reference[p] == e for p, e in setup["known_factors"].items())
        assert math.prod(p**e for p, e in setup["known_factors"].items())*setup["unresolved_residual"] == control["N"]-1
        if "certified_order" in control:
            assert int(n_order(control["base"], control["N"])) == control["certified_order"]
        assert control["metrics"]["geometric_rows"] == 0
    kernel_row_comparisons = 0
    for n in (35, 77, 143, 299, 697):
        width = PREFIX["sixth_width"](n)
        for base in sorted(set(range(2, min(n, 30))) | {n-1}):
            if math.gcd(n, base) != 1 or pow(base, n-1, n) != 1:
                continue
            length = 3*width*width+1
            roots = [pow(base, u, n) for u in range(length)]
            for a in range(1, width+1):
                label = a+width*width
                target = pow(base, a*n+width*width, n)
                assert target == pow(base, label, n) and label < length
                assert math.prod(target-root for root in roots) % n == 0
                cofactors = [math.prod(target-roots[v] for v in range(length) if v != u) % n
                             for u in range(length)]
                derivative = sum(cofactors) % n
                marked = -sum(u*roots[u]*cofactors[u] for u in range(length)) % n
                assert marked == -label*target*derivative % n
                kernel_row_comparisons += 1
    square_preprocess_cases = 0
    for prime in primerange(2, 150):
        result = public_pass(prime*prime)
        assert result["status"] == "square-factor" and result["factor"] == prime
        assert result["preprocessing_metrics"] == dict(square_root_queries=1, square_gcds=1)
        square_preprocess_cases += 1
    first_jet_cancellations = zero_endpoint_first_jets = 0
    for n in (35, 49, 77, 101):
        for alpha in range(7):
            for length in range(2, 11):
                roots = [pow(alpha, u, n) for u in range(length)]
                for label in range(length-1):
                    x, shifted = roots[label], roots[label+1]
                    def derivative_at(target):
                        return sum(math.prod(target-roots[v] for v in range(length) if v != u)
                                   for u in range(length)) % n
                    left = alpha*derivative_at(shifted)*(shifted-pow(alpha, length, n)) % n
                    right = pow(alpha, length, n)*(shifted-1)*derivative_at(x) % n
                    assert left == right
                    first_jet_cancellations += 1
                    zero_endpoint_first_jets += int((shifted-pow(alpha, length, n)) % n == 0
                                                    or (shifted-1) % n == 0)
    deliberately_short = public_pass(1373653, 2)
    assert deliberately_short["staged_pass"]["status"] == "no-raw-seed"
    assert deliberately_short["factor"] == 1657
    return dict(retained_source_comparisons=retained_comparisons,
                saturated_residual_column_values=saturated_reductions,
                partial_factorizations=partial_factorizations,
                rough_prime_certificates=certified_primes, unresolved_setup_tails=unresolved_tails,
                zero_wrap_reconstructions=zero_wrap_cases, bounded_wrap_reconstructions=wrap_bound_cases,
                square_reconstructions=square_cases,
                square_preprocess_cases=square_preprocess_cases,
                cleared_first_jet_cancellations=first_jet_cancellations,
                zero_endpoint_first_jet_cancellations=zero_endpoint_first_jets,
                saturated_kernel_row_and_mark_comparisons=kernel_row_comparisons, controls=controls,
                deliberately_short_scan_rescued=deliberately_short,
                literal_wrapped_base_provenance="Offline diagnostic control; public rescue receives N and base only. No guarantee is claimed that a small automatic menu supplies this base.")


def source_inventory():
    parent = json.loads((ROOT/PARENT).read_text())
    for path, expected in parent["source_sha256"].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path
    paths = set(parent["source_sha256"])
    paths.update((PARENT, "RiemannGaussian/SemiprimeCommonOrder.lean",
                  "scripts/CheckSemiprimeCommonOrder.lean",
                  "scripts/probe_semiprime_common_order.py"))
    return {path: hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in sorted(paths)}


def replay():
    validation = validate()
    parent = json.loads((ROOT/PARENT).read_text())
    cases = []
    for prior in parent["inputs"]:
        n = prior["N"]
        actual = public_pass(n)
        baseline = STAGED["seeded_source_pass"](n)
        assert actual["factor"] is not None or baseline["factor"] is None
        actual.update(regime=prior["regime"], reference_p=prior["reference_p"],
                      reference_q=prior["reference_q"], input_bits=n.bit_length(),
                      fresh_staged_baseline=baseline)
        cases.append(actual)
    return dict(seed=SEED, scope="raw-kernel global orders, retained N-1 prefix and quadratic wrap labels",
                is_complete_semiprime_factorizer=False, is_bit_complexity_certificate=False,
                one_sixth_guarantee="OPEN", validation=validation, inputs=cases,
                input_count=len(cases), recovered_count=sum(c["factor"] is not None for c in cases),
                summary={s: sum(c["status"] == s for c in cases) for s in sorted({c["status"] for c in cases})},
                source_sha256=source_inventory(),
                timing_protocol="One complete charged public pass and one fresh staged baseline per saved input. Kernel controls charge raw tests, one N-1 polynomial, every residual reduction/GCD, trial divisor, order power, certificate check and quadratic candidate. Oracle validation is outside timing.",
                limitations="Exact order extraction may leave a rough unresolved part, and a known common order may be too small for the bounded wrap guarantee. Sixth-root raw-menu coverage and nonkernel residual acquisition remain open. Python/backend bit costs and the full runtime algorithm are not certified in Lean.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = replay()
    if args.output:
        args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in
                      ("input_count", "recovered_count", "summary", "one_sixth_guarantee")}, indent=2))


if __name__ == "__main__":
    main()
