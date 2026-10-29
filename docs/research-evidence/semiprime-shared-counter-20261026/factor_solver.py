"""Uniform factor-search wrapper for the actual macro-FFT network and counter.

The numerical guard chooses either exact divisor scanning or the constructed
shared-summary counter. The former is a finite-input fallback in the proposed
asymptotic proof, and is explicitly reported in the result. Passing its tests
does not certify the asymptotic theorem or make the counter practical.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt

import factor_network
from shared_parameters import scheduled_guard, scope_statistics


@dataclass(frozen=True)
class FactorResult:
    N: int
    factors: tuple | None
    method: str
    count_queries: int
    guard_reasons: tuple


def direct_factor(N):
    """Exact, polynomial-space finite-size fallback; no factor oracle."""
    if N % 2 == 0:
        return (2, N // 2) if N > 2 else None
    for p in range(3, isqrt(N) + 1, 2):
        if N % p == 0:
            return p, N // p
    return None


def recover_from_counter(network, count_network):
    """Recover one factor with <= L+1 exact conditional counts.

    count_network must return the contraction of its argument's actual local
    tensors. Only P's original L bits are restricted. The uniqueness of the
    network's internal extension leaves Q determined by P*Q=N.
    """
    queries = 1
    total = count_network(network)
    if type(total) is not int or total < 0:
        raise ArithmeticError("counter did not return a nonnegative integer")
    if total == 0:
        return None, queries
    fixed = {}
    P = 0
    for i, edge in enumerate(network.input_bits['P']):
        candidate = dict(fixed)
        candidate[edge] = 0
        zero = count_network(network.restrict(candidate))
        queries += 1
        if type(zero) is not int or not 0 <= zero <= total:
            raise ArithmeticError("conditional count violates its parent count")
        if zero:
            fixed[edge] = 0
            total = zero
        else:
            fixed[edge] = 1
            P |= 1 << i
            # C_parent = C_zero + C_one, so the known positive total is unchanged.
    if not 2 <= P < network.N or network.N % P:
        raise ArithmeticError("conditional counts did not recover a divisor")
    return (P, network.N // P), queries


def count_network_with_layout(network, layout):
    from shared_counter import Factor, count
    factors = tuple(Factor(v.ports, v.entry) for v in network.vertices)
    return count(len(network.edges), factors, layout, validate_design=True,
                 require_quantitative=True).value


def factor(N):
    if type(N) is not int or N < 2:
        raise ValueError("N must be an integer at least 2")
    network = factor_network.compile(N)
    scopes = tuple(v.ports for v in network.vertices)
    stats = scope_statistics(len(network.edges), scopes)
    if stats['incidence'] != 2 * stats['n'] or stats['occurrence'] != 2:
        raise ArithmeticError("macro-FFT network lost its two-endpoint invariant")
    guard = scheduled_guard(**stats)
    if not guard.accepted:
        return FactorResult(N, direct_factor(N), "direct finite-size fallback", 0,
                            guard.reasons)
    from shared_layout import build_layout
    p = guard.parameters
    layout = build_layout(stats['n'], scopes, p.r, p.Q, p.R, p.A0,
                          tau=Fraction(1, p.tau_denominator), require_lemma=True)
    factors, queries = recover_from_counter(
        network, lambda net: count_network_with_layout(net, layout))
    return FactorResult(N, factors, "constructed shared-summary counter", queries, ())
