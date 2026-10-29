"""Exact, uniform parameter policy for the generic shared-summary counter.

Only integer arithmetic is used. A failed guard means use the finite-size
fallback, not assume that an invalid layout has the advertised complexity.
The eventual validity for w=O(n**(3/4)), b=2 is proved in the accompanying
resource derivation; this module does not claim to be its Lean certificate.
"""
from dataclasses import dataclass
from math import isqrt


def ceil_log2(n):
    if not isinstance(n, int) or isinstance(n, bool) or n < 1:
        raise ValueError("ceil_log2 requires a positive integer")
    return (n - 1).bit_length()


@dataclass(frozen=True)
class Parameters:
    r: int
    Q: int
    R: int
    A0: int
    tau_denominator: int

    @property
    def D(self):
        return self.r ** (2 * self.Q)


@dataclass(frozen=True)
class GuardResult:
    accepted: bool
    reasons: tuple
    parameters: Parameters | None
    tail_numerator: int | None = None
    tail_denominator: int | None = None


def binomial_tail(r, Q, A0, R):
    """Exact numerator/denominator for Bin(Q,(r-1)/(2r)) outside I.

    Streaming consecutive terms avoids both factorials and a probability list.
    The recurrence division is exact for each individual binomial term.
    """
    if r < 2 or Q < 1 or R < 1 or A0 < 0 or A0 + R - 1 > Q:
        raise ValueError("invalid binomial interval")
    denominator = (2 * r) ** Q
    term = (r + 1) ** Q
    total = tail = 0
    for k in range(Q + 1):
        total += term
        if not A0 <= k < A0 + R:
            tail += term
        if k < Q:
            numerator = term * (Q - k) * (r - 1)
            divisor = (k + 1) * (r + 1)
            term, remainder = divmod(numerator, divisor)
            if remainder:
                raise ArithmeticError("nonintegral binomial recurrence")
    if total != denominator:
        raise ArithmeticError("binomial normalization failure")
    return tail, denominator


def check_guard(n, incidence, occurrence, arity, parameters):
    """Check the literal hypotheses of Lemma 4.7, with tau=1/tau_denominator.

    Scope statistics are supplied here; the caller computes them from its
    actual wiring. No claim about an unexamined scope family is made.
    """
    values = (n, incidence, occurrence, arity, parameters.r, parameters.Q,
              parameters.R, parameters.A0, parameters.tau_denominator)
    if any(not isinstance(x, int) or isinstance(x, bool) for x in values):
        raise ValueError("integer parameters required")
    p = parameters
    reasons = []
    if min(n, occurrence, arity) < 1:
        reasons.append("positive dimensions")
    if not n <= incidence <= occurrence * n:
        reasons.append("incidence bounds")
    if p.r < 2 or not 1 <= p.R < p.Q or p.tau_denominator < 2:
        reasons.append("parameter range")
    if p.A0 < 0 or p.A0 + p.R - 1 > p.Q:
        reasons.append("tail interval")
    if reasons:
        return GuardResult(False, tuple(reasons), p)
    D = p.D
    if 2 * (occurrence + arity) * D * D > incidence:
        reasons.append("incidence load balance")
    if 2 * p.Q * p.r * p.r > n:
        reasons.append("variable group balance")
    tail, denominator = binomial_tail(p.r, p.Q, p.A0, p.R)
    if tail * p.tau_denominator * p.r * occurrence > denominator:
        reasons.append("binomial spectral tail")
    return GuardResult(not reasons, tuple(reasons), p, tail, denominator)


def scheduled_guard(n, incidence, occurrence, arity):
    """The beta=1 numerical schedule, tested directly at growing arity.

    This does not invoke Lemma 4.8's polylogarithmic-arity premise.
    Any failure is explicit. The caller must retain an exact fallback.
    """
    lam = ceil_log2(n)
    if lam < 2:
        return GuardResult(False, ("small logarithm",), None)
    nu = ceil_log2(lam)
    r = isqrt(lam) // (nu * nu)
    Q = lam // (128 * nu)
    sqrt_ceil = isqrt(lam) + int(isqrt(lam) ** 2 != lam)
    R = 4 * sqrt_ceil
    if r < 2 or Q <= R:
        return GuardResult(False, ("schedule range",), None)
    A0 = (Q * (r - 1) - r * (R - 1)) // (2 * r)
    p = Parameters(r, Q, R, A0, r * lam)
    if R < 32 or 6 * R > Q:
        return GuardResult(False, ("schedule concentration range",), p)
    return check_guard(n, incidence, occurrence, arity, p)


def scope_statistics(n, scopes):
    """Compute scope sizes/incidence; reject repeated ports in a factor."""
    if not isinstance(n, int) or isinstance(n, bool) or n < 0:
        raise ValueError("invalid variable count")
    occurrences = [0] * n
    incidence = arity = 0
    for scope in scopes:
        if len(set(scope)) != len(scope):
            raise ValueError("repeated variable in a factor scope")
        arity = max(arity, len(scope))
        incidence += len(scope)
        for v in scope:
            if not isinstance(v, int) or isinstance(v, bool) or not 0 <= v < n:
                raise ValueError("invalid scope variable")
            occurrences[v] += 1
    return dict(n=n, incidence=incidence, occurrence=max(occurrences, default=0),
                arity=arity)
