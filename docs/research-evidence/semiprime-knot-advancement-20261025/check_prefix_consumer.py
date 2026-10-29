#!/usr/bin/env python3
"""Check the prefix consumer with a deliberately slow oracle; no rate claim.

Small fixtures isolate central/signed CRT branches. They are not instances
of the full native order-screened catalogue or a coverage experiment.
"""
from math import gcd


def trace_polynomial(nodes, modulus, value):
    result = 1
    for x in nodes:
        result = result * (value - x - pow(x, -1, modulus)) % modulus
    return result


def slow_alexander_prefix(nodes, modulus, q, length):
    normalization = pow(trace_polynomial(nodes, modulus, 2), -1, modulus)
    result, power = 1, 1
    for _ in range(length):
        power = power * q % modulus
        trace = (power + pow(power, -1, modulus)) % modulus
        result = result * trace_polynomial(nodes, modulus, trace) * normalization % modulus
    return result


def recover(modulus, beta, stride, horizon, exponents, prefix_hit):
    """Use either exact prefix nonunitness or zero, with its coverage premise."""
    assert horizon >= 1
    assert all(e % stride != 0 or abs(e // stride) > horizon for e in exponents)
    nodes = [pow(beta, e, modulus) for e in exponents]
    for e, x in zip(exponents, nodes):
        common = gcd(x - 1, modulus)
        if 1 < common < modulus:
            return ("factor", common, "central")
        if common == modulus:
            assert e != 0
            return ("annihilator", e, "central")

    # Coverage supplies hi=true; no oracle call at the known endpoint.
    lo, hi = 0, horizon
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if prefix_hit(mid):
            hi = mid
        else:
            lo = mid
    q = pow(beta, stride, modulus)
    for sign in (1, -1):
        target = pow(q, sign * hi, modulus)
        for e, x in zip(exponents, nodes):
            common = gcd(x - target, modulus)
            if 1 < common < modulus:
                return ("factor", common, sign * hi)
            if common == modulus:
                exponent = e - stride * sign * hi
                assert exponent != 0
                return ("annihilator", exponent, sign * hi)
    raise AssertionError("Supplied prefix decision or coverage premise was false")


def main():
    modulus, stride, horizon = 77, 1, 2
    cases = [
        (2, (4,), "factor", 7, 1),
        (2, (19,), "factor", 7, 1),  # Opposite signs at the two local primes.
        (2, (31,), "annihilator", 30, 1),
        (2, (29,), "annihilator", 30, -1),
        (2, (30,), "annihilator", 30, "central"),
        (2, (18,), "factor", 7, "central"),
        (2, (4, 32), "factor", 7, 1),  # Saturated full prefix, proper earlier prefix.
        (3, (32,), "annihilator", 30, 2),  # First prefix is a unit.
    ]
    norm_checks = 0
    for beta, exponents, tag, value, seed in cases:
        nodes = [pow(beta, e, modulus) for e in exponents]
        calls = []
        central_unit = all(gcd(x - 1, modulus) == 1 for x in nodes)
        if central_unit:
            bits = []
            for length in range(horizon + 1):
                residue = slow_alexander_prefix(nodes, modulus, beta, length)
                direct = 1
                for x in nodes:
                    for i in range(1, length + 1):
                        direct = (direct * (x - pow(beta, i, modulus))
                                  * (x - pow(beta, -i, modulus))
                                  * pow((x - 1) ** 2, -1, modulus)) % modulus
                assert residue == direct
                norm_checks += 1
                bits.append(gcd(residue, modulus) != 1)
            assert bits[0] is False and bits[-1] is True
            assert bits == sorted(bits)

        def oracle(length):
            calls.append(length)
            assert central_unit and 0 < length < horizon
            return gcd(slow_alexander_prefix(nodes, modulus, beta, length), modulus) != 1

        result = recover(modulus, beta, stride, horizon, exponents, oracle)
        assert result == (tag, value, seed), (exponents, result)
        if tag == "factor":
            assert 1 < value < modulus and modulus % value == 0
        else:
            assert value != 0 and pow(beta, value, modulus) == 1
        assert len(calls) <= 1
        if seed == "central":
            assert not calls
    zero_cases = [
        (2, (19,), ("factor", 7, 1)),
        (2, (31,), ("annihilator", 30, 1)),
        (2, (29,), ("annihilator", 30, -1)),
        (2, (4, 22), ("factor", 11, 2)),  # Earlier prefix is nonzero but nonunit.
        (3, (32,), ("annihilator", 30, 2)),
    ]
    for beta, exponents, expected in zero_cases:
        nodes = [pow(beta, e, modulus) for e in exponents]
        assert all(gcd(x - 1, modulus) == 1 for x in nodes)
        assert slow_alexander_prefix(nodes, modulus, beta, horizon) == 0
        calls = []

        def zero_oracle(length):
            calls.append(length)
            return slow_alexander_prefix(nodes, modulus, beta, length) == 0

        result = recover(modulus, beta, stride, horizon, exponents, zero_oracle)
        assert result == expected, (exponents, result)
        assert len(calls) <= 1
        if exponents == (4, 22):
            earlier = slow_alexander_prefix(nodes, modulus, beta, 1)
            assert earlier != 0 and gcd(earlier, modulus) == 7
    print(f"PASS: {len(cases)} nonunit-prefix CRT fixtures; {norm_checks} exact norm checks")
    print(f"PASS: {len(zero_cases)} zero-only prefix CRT fixtures")
    print("Oracle is deliberately slow; no native coverage or fast-acquisition claim.")


if __name__ == "__main__":
    main()
