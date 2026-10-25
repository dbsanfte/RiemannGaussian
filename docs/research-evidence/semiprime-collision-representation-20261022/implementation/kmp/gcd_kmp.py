"""Exact gcd-aware KMP over explicit residue arrays. No native-source acquisition."""
from dataclasses import dataclass
from math import gcd, isqrt

@dataclass(frozen=True)
class Result:
    factor: int | None
    positions: tuple[int, ...]
    comparisons: int

class _FactorFound(Exception):
    def __init__(self, factor):
        self.factor = factor

class _Comparator:
    def __init__(self, modulus):
        self.modulus = modulus
        self.count = 0

    def equal(self, a, b):
        self.count += 1
        g = gcd(a - b, self.modulus)
        if 1 < g < self.modulus:
            raise _FactorFound(g)
        return g == self.modulus

def _validate(modulus, *arrays):
    if type(modulus) is not int or modulus < 2:
        raise ValueError("modulus must be an integer >= 2")
    converted = []
    for array in arrays:
        values = tuple(array)
        if any(type(x) is not int for x in values):
            raise ValueError("array entries must be integers")
        converted.append(tuple(x % modulus for x in values))
    return converted

def _match(pattern, text, cmp):
    d = len(pattern)
    if d == 0:
        return tuple(range(len(text) + 1))
    pi = [0] * d
    q = 0
    for i in range(1, d):
        while True:
            if cmp.equal(pattern[i], pattern[q]):
                q += 1
                break
            if q == 0:
                break
            q = pi[q - 1]
        pi[i] = q
    found = []
    q = 0
    for i, value in enumerate(text):
        while True:
            if cmp.equal(value, pattern[q]):
                q += 1
                break
            if q == 0:
                break
            q = pi[q - 1]
        if q == d:
            found.append(i + 1 - d)
            q = pi[q - 1]
    return tuple(found)

def match(modulus, pattern, text):
    """Return factor, or exact occurrences simultaneously modulo all prime divisors.

    Empty pattern occurs at every boundary. Factor results carry no partial matches.
    Squarefreeness is a theorem hypothesis, not checked by factoring the modulus.
    """
    pattern, text = _validate(modulus, pattern, text)
    cmp = _Comparator(modulus)
    try:
        positions = _match(pattern, text, cmp)
    except _FactorFound as exc:
        return Result(exc.factor, (), cmp.count)
    return Result(None, positions, cmp.count)

def cyclic_match(modulus, source, target):
    """Positions r where target[k]=source[(k+r)%d]; equal lengths required.

    For two empty arrays the sole canonical cyclic offset is 0.
    """
    source, target = _validate(modulus, source, target)
    if len(source) != len(target):
        raise ValueError("cyclic arrays must have equal lengths")
    if not source:
        return Result(None, (0,), 0)
    return match(modulus, target, source + source[:-1])

def _prime_divisors(n):
    out = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out

def automorphism_matches(modulus, prime, primitive_root, source, target):
    """Find j with target=rho_j(source) in R[X]/(X^prime-1).

    Coefficients are indexed by exponent; rho_j sends X to X^j.
    Returns j values in Result.positions (not cyclic offsets). Prime and root
    metadata are checked in O(prime) arithmetic work; no hidden factor supplied.
    """
    source, target = _validate(modulus, source, target)
    if type(prime) is not int or prime < 3 or prime % 2 == 0:
        raise ValueError("prime must be an odd prime")
    if any(prime % p == 0 for p in range(2, isqrt(prime) + 1)):
        raise ValueError("prime must be prime")
    if len(source) != prime or len(target) != prime:
        raise ValueError("coefficient arrays must have length prime")
    if type(primitive_root) is not int:
        raise ValueError("primitive root must be an integer")
    root = primitive_root % prime
    if root == 0 or any(pow(root, (prime-1)//p, prime) == 1
                        for p in _prime_divisors(prime-1)):
        raise ValueError("root is not primitive")
    cmp = _Comparator(modulus)
    try:
        if not cmp.equal(source[0], target[0]):
            return Result(None, (), cmp.count)
        indices = [1]
        for _ in range(prime-2):
            indices.append(indices[-1] * root % prime)
        a = tuple(source[k] for k in indices)
        b = tuple(target[k] for k in indices)
        offsets = _match(b, a + a[:-1], cmp)
        inverse_root = pow(root, -1, prime)
        positions = tuple(pow(inverse_root, r, prime) for r in offsets)
        return Result(None, positions, cmp.count)
    except _FactorFound as exc:
        return Result(exc.factor, (), cmp.count)
