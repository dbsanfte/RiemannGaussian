"""Independent exact arithmetic helpers for inverse-prefix compression audits.

Arithmetic arrays use index zero as a zero sentinel. Finite convolution
inputs are zero-padded; prefix outputs also have a zero sentinel. No producer
module is imported. These routines evaluate identities, not global bounds.
"""

from fractions import Fraction


def _integer(value, name, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f"{name} must be an integer >= {minimum}")
    return value


def _array(values):
    if not values:
        raise ValueError("arithmetic arrays require a zero sentinel")
    # Floats would silently import binary approximations into exact audits.
    if any(isinstance(value, float) for value in values):
        raise TypeError("use integers, rational strings, or Fraction, not float")
    result = [Fraction(value) for value in values]
    if result[0] != 0:
        raise ValueError("index zero must be zero")
    return result


def convolution(a, b, N):
    """Dirichlet convolution through N, via independent product-index loops.

    Coefficients beyond either supplied finite array are interpreted as zero.
    The result has length N+1 and consists of Fractions.
    """
    _integer(N, "N")
    a, b = _array(a), _array(b)
    result = [Fraction(0) for _ in range(N + 1)]
    for i in range(1, min(N, len(a) - 1) + 1):
        if not a[i]:
            continue
        for j in range(1, min(N // i, len(b) - 1) + 1):
            if b[j]:
                result[i * j] += a[i] * b[j]
    return result


def inverse(h):
    """Inverse of unit-normalized h by a finite formal geometric expansion.

    For g=delta-h, g(1)=0, so g^{*r} has support n>=2**r.
    Hence sum_{r=0}^{floor(log2 N)} g^{*r} is the inverse through N.
    This uses no coefficient-by-coefficient divisor recurrence.
    """
    h = _array(h)
    N = len(h) - 1
    if N < 1 or h[1] != 1:
        raise ValueError("inverse requires h[1]=1 and at least two entries")
    delta = [Fraction(0) for _ in range(N + 1)]
    delta[1] = Fraction(1)
    g = [delta[n] - h[n] for n in range(N + 1)]
    result = delta[:]
    term = delta
    for _ in range(N.bit_length() - 1):
        term = convolution(term, g, N)
        result = [left + right for left, right in zip(result, term)]
    return result


def prime_mu(N):
    """Mobius coefficients from independent prime and square-factor sieves."""
    _integer(N, "N")
    mu = [1 for _ in range(N + 1)]
    mu[0] = 0
    composite = [False for _ in range(N + 1)]
    for p in range(2, N + 1):
        if composite[p]:
            continue
        for n in range(p, N + 1, p):
            mu[n] = -mu[n]
            composite[n] = True
        for n in range(p * p, N + 1, p * p):
            mu[n] = 0
    return mu


def prefix(a):
    """Return the usual inclusive prefix sums, preserving the zero sentinel."""
    a = _array(a)
    result = [Fraction(0)]
    total = Fraction(0)
    for value in a[1:]:
        total += value
        result.append(total)
    return result


def truncated_components(h, a, u, k, N):
    """Return k prefix tables for a_u^{*r} * h^{*(r-1)}, r=1..k.

    Table index r-1 holds the rth component; its own index n is inclusive.
    Here a_u agrees with a for 1<=n<=u and is zero elsewhere. h must
    supply every coefficient through N. a only needs coefficients through
    min(u,N). No inverse identity is assumed or established by this helper.
    """
    _integer(u, "u")
    _integer(k, "k", 1)
    _integer(N, "N", 1)
    h, a = _array(h), _array(a)
    if len(h) <= N or len(a) <= min(u, N):
        raise ValueError("insufficient supplied arithmetic coefficients")
    truncated = [Fraction(0) for _ in range(N + 1)]
    for n in range(1, min(u, N) + 1):
        truncated[n] = a[n]
    # Multiplying successive components by a_u*h changes r to r+1.
    step = convolution(truncated, h, N)
    component = truncated
    tables = []
    for r in range(1, k + 1):
        tables.append(prefix(component))
        if r < k:
            component = convolution(component, step, N)
    return tables


def safe_cutoff(X, k):
    """Minimal u>=0 satisfying (u+1)**k > 4*X-1, exactly.

    k=1 returns 4*X-1. A nonunit omitted tail supported on n>=u+1
    has kth convolution supported on n>4*X-1. The separate inverse
    condition a*h=delta is necessary for the compression identity.
    """
    _integer(X, "X", 1)
    _integer(k, "k", 1)
    target = 4 * X - 1
    # If k reaches the binary length, 2**k exceeds target. Since 1**k
    # cannot exceed target>=3, the minimal cutoff is exactly one. Compare
    # binary lengths without constructing a potentially enormous power.
    if k >= target.bit_length():
        return 1
    lower, upper = 1, target + 1
    while lower < upper:
        middle = (lower + upper) // 2
        if middle ** k > target:
            upper = middle
        else:
            lower = middle + 1
    return lower - 1


def signed_block_energies(prefix_a, X):
    """Exact half-open integer block energies from inclusive prefix sums."""
    _integer(X, "X", 1)
    sums = _array(prefix_a)
    if len(sums) < 4 * X:
        raise ValueError("prefix sums must include index 4*X-1")
    parent = sum((sums[n] ** 2 for n in range(X, 2 * X)), Fraction(0))
    child = sum((sums[n] ** 2 for n in range(2 * X, 4 * X)), Fraction(0))
    return {"A_X": parent, "A_2X": child, "Delta": child - 4 * parent}


def solve_unique(A, b):
    """Solve a rectangular exact linear system with a unique solution.

    Return a list of Fractions. Raise ValueError for inconsistent systems,
    nonunique systems, or malformed dimensions. Input arrays are not mutated.
    """
    if len(A) != len(b):
        raise ValueError("matrix and right-hand-side row counts differ")
    columns = len(A[0]) if A else 0
    if any(len(row) != columns for row in A):
        raise ValueError("matrix rows have different lengths")
    if any(isinstance(value, float) for row in A for value in row) or any(
        isinstance(value, float) for value in b
    ):
        raise TypeError("exact elimination does not accept floats")
    rows = [[Fraction(v) for v in row] + [Fraction(rhs)]
            for row, rhs in zip(A, b)]
    pivot_rows = {}
    cursor = 0
    for column in range(columns):
        pivot = next((r for r in range(cursor, len(rows))
                      if rows[r][column]), None)
        if pivot is None:
            continue
        rows[cursor], rows[pivot] = rows[pivot], rows[cursor]
        scale = rows[cursor][column]
        rows[cursor] = [v / scale for v in rows[cursor]]
        for r in range(len(rows)):
            if r == cursor or not rows[r][column]:
                continue
            multiplier = rows[r][column]
            rows[r] = [left - multiplier * right
                       for left, right in zip(rows[r], rows[cursor])]
        pivot_rows[column] = cursor
        cursor += 1
    if any(all(v == 0 for v in row[:columns]) and row[-1] != 0
           for row in rows):
        raise ValueError("inconsistent linear system")
    if len(pivot_rows) != columns:
        raise ValueError("linear system does not have a unique solution")
    return [rows[pivot_rows[column]][-1] for column in range(columns)]
