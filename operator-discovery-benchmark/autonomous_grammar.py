"""A finite, typed program language, independent of named arithmetic operators.

Indices are 1..N; out-of-range sequence access is unavailable. Matrix maps use
the whole declared N by N domain, so lookahead up to N is explicit. Integer
quotient/remainder use Python's floor convention. Bounded sums are clamped to
0..N. Singular matrices and zero index divisors reject an evaluation. No prime,
factorization, multiplicativity, analytic continuation or zero oracle exists.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json

VERSION = "finite-typed-programs-v1"
TYPES = ("index", "boolean", "scalar", "map", "sequence")
PRODUCTIONS = {
    "index": ["v", "int", "ia", "is", "im", "iq", "ir"],
    "boolean": ["eq", "le", "lt", "and", "not"],
    "scalar": ["q", "embed", "indicator", "sadd", "smul", "bsum"],
    "map": ["kernel", "madd", "mscale", "mcompose", "minverse"],
    "sequence": ["input", "tab", "apply", "pair", "add", "scale", "point", "norm2"],
}


@dataclass(frozen=True)
class Gaussian:
    """Exact Q(i), only used on complex inputs; real work stays in Q."""
    real: Q
    imag: Q = Q(0)

    @staticmethod
    def lift(x):
        return x if isinstance(x, Gaussian) else Gaussian(Q(x))

    def __add__(self, other):
        other = self.lift(other)
        return Gaussian(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self):
        return Gaussian(-self.real, -self.imag)

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        other = self.lift(other)
        return Gaussian(self.real * other.real - self.imag * other.imag,
                        self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.lift(other)
        d = other.real * other.real + other.imag * other.imag
        if not d:
            raise ValueError("zero scalar divisor")
        return self * Gaussian(other.real / d, -other.imag / d)

    def __rtruediv__(self, other):
        return self.lift(other) / self

    def __bool__(self):
        return bool(self.real or self.imag)


def norm2(x):
    return x.real * x.real + x.imag * x.imag if isinstance(x, Gaussian) else x * x


def encode(x):
    if isinstance(x, Gaussian):
        return [x.real.numerator, x.real.denominator, x.imag.numerator, x.imag.denominator]
    x = Q(x)
    return [x.numerator, x.denominator, 0, 1]


def decode(x):
    if not isinstance(x, list) or len(x) != 4 or any(type(v) is not int for v in x):
        raise ValueError("expected exact rational-complex quadruple")
    a, b = Q(x[0], x[1]), Q(x[2], x[3])
    return Gaussian(a, b) if b else a


def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(",", ":"), allow_nan=False)


def digest(x):
    return hashlib.sha256(canonical(x).encode()).hexdigest()


def expanded(term, macros):
    def go(t, seen):
        if t[0] == "macro":
            if t[1] in seen or t[1] not in macros:
                raise ValueError("cyclic or unknown macro")
            return go(macros[t[1]]["body"], seen | {t[1]})
        return [t[0]] + [go(x, seen) if isinstance(x, list) else x for x in t[1:]]
    return go(term, set())


def cost(t):
    return 1 + sum(cost(x) for x in t[1:] if isinstance(x, list))


def subterms(t):
    yield t
    for child in t[1:]:
        if isinstance(child, list):
            yield from subterms(child)


def infer(t, scope=frozenset(), macros=None):
    macros = macros or {}
    if not isinstance(t, list) or not t or not isinstance(t[0], str):
        raise ValueError("invalid AST")
    op = t[0]
    if op == "macro":
        if len(t) != 2:
            raise ValueError("bad macro arity")
        return infer(expanded(t, macros), scope)
    if op in {"v", "int", "input"}:
        if len(t) != 2:
            raise ValueError("leaf arity")
        if op == "v" and t[1] not in scope | {"N"}:
            raise ValueError("unbound index")
        if op in {"int", "input"} and type(t[1]) is not int:
            raise ValueError("integer leaf required")
        if op == "input" and t[1] not in (0, 1):
            raise ValueError("unknown input slot")
        return "sequence" if op == "input" else "index"
    if op == "q":
        if len(t) != 3 or any(type(x) is not int for x in t[1:]) or t[2] <= 0:
            raise ValueError("rational scalar required")
        return "scalar"
    signatures = {**{o: ("index", ["index", "index"]) for o in ("ia", "is", "im", "iq", "ir")},
                  **{o: ("boolean", ["index", "index"]) for o in ("eq", "le", "lt")},
                  "and": ("boolean", ["boolean", "boolean"]), "not": ("boolean", ["boolean"]),
                  "embed": ("scalar", ["index"]), "indicator": ("scalar", ["boolean"]),
                  "sadd": ("scalar", ["scalar", "scalar"]), "smul": ("scalar", ["scalar", "scalar"]),
                  "madd": ("map", ["map", "map"]), "mscale": ("map", ["scalar", "map"]),
                  "mcompose": ("map", ["map", "map"]), "minverse": ("map", ["map"]),
                  "apply": ("sequence", ["map", "sequence"]), "add": ("sequence", ["sequence", "sequence"]),
                  "scale": ("sequence", ["scalar", "sequence"]), "point": ("sequence", ["sequence", "sequence"]),
                  "norm2": ("sequence", ["sequence"])}
    if op == "bsum":
        if len(t) != 4 or t[1] not in {"j", "r"} or t[1] in scope:
            raise ValueError("bounded-sum binding")
        if infer(t[2], scope, macros) != "index" or infer(t[3], scope | {t[1]}, macros) != "scalar":
            raise ValueError("bounded-sum types")
        return "scalar"
    if op in {"kernel", "tab", "pair"}:
        expected_len = 4 if op == "pair" else 2
        local = {"n", "i", "j"} if op == "pair" else ({"n", "i"} if op == "kernel" else {"n"})
        if len(t) != expected_len or infer(t[1], frozenset(local), macros) != "scalar":
            raise ValueError("representation-map types")
        if op == "pair" and any(infer(x, scope, macros) != "sequence" for x in t[2:]):
            raise ValueError("pair inputs")
        return "map" if op == "kernel" else "sequence"
    if op not in signatures:
        raise ValueError("unknown production")
    output, inputs = signatures[op]
    if len(t) != len(inputs) + 1 or any(infer(x, scope, macros) != want for x, want in zip(t[1:], inputs)):
        raise ValueError("production types")
    return output


class Budget:
    def __init__(self, maximum):
        self.remaining = maximum
        self.used = 0

    def step(self, count=1):
        self.remaining -= count
        self.used += count
        if self.remaining < 0:
            raise ValueError("operation budget exhausted")


def scalar(t, env, budget):
    budget.step()
    o = t[0]
    if o == "v": return env[t[1]]
    if o == "int": return t[1]
    if o == "q": return Q(t[1], t[2])
    if o in {"embed", "indicator", "not"}:
        x = scalar(t[1], env, budget)
        return Q(x) if o == "embed" else (Q(int(x)) if o == "indicator" else not x)
    if o == "bsum":
        bound = min(env["N"], max(0, scalar(t[2], env, budget)))
        return sum((scalar(t[3], dict(env, **{t[1]: j}), budget) for j in range(1, bound + 1)), Q(0))
    a, b = scalar(t[1], env, budget), scalar(t[2], env, budget)
    if o in {"ia", "sadd"}: return a + b
    if o == "is": return a - b
    if o in {"im", "smul"}: return a * b
    if o in {"iq", "ir"}:
        if not b: raise ValueError("zero index divisor")
        return a // b if o == "iq" else a % b
    if o == "eq": return a == b
    if o == "le": return a <= b
    if o == "lt": return a < b
    if o == "and": return a and b
    raise ValueError("unknown scalar operation")


def matrix(t, N, budget, inverse_max):
    o = t[0]
    if o == "kernel":
        return [[scalar(t[1], {"n": n, "i": i, "N": N}, budget) for i in range(1, N + 1)]
                for n in range(1, N + 1)]
    if o == "mscale":
        a = scalar(t[1], {"N": N}, budget)
        return [[a * x for x in row] for row in matrix(t[2], N, budget, inverse_max)]
    left = matrix(t[1], N, budget, inverse_max)
    if o == "minverse":
        if N > inverse_max: raise ValueError("declared matrix-inverse dimension exceeded")
        rows = [row[:] + [Q(i == j) for j in range(N)] for i, row in enumerate(left)]
        for c in range(N):
            pivot = next((r for r in range(c, N) if rows[r][c]), None)
            if pivot is None: raise ValueError("singular matrix")
            rows[c], rows[pivot] = rows[pivot], rows[c]
            a = rows[c][c]
            budget.step(2 * N)
            rows[c] = [x / a for x in rows[c]]
            for r in range(N):
                if r != c and rows[r][c]:
                    a = rows[r][c]
                    budget.step(2 * N)
                    rows[r] = [x - a * y for x, y in zip(rows[r], rows[c])]
        return [row[N:] for row in rows]
    right = matrix(t[2], N, budget, inverse_max)
    if o == "madd":
        budget.step(N * N)
        return [[x + y for x, y in zip(a, b)] for a, b in zip(left, right)]
    budget.step(N ** 3)
    return [[sum((left[n][k] * right[k][i] for k in range(N)), Q(0)) for i in range(N)] for n in range(N)]


def evaluate(term, inputs, *, macros=None, operations=2_000_000, inverse_max=128):
    if len(inputs) != 2 or not inputs[0] or len(inputs[0]) != len(inputs[1]):
        raise ValueError("two equal nonempty finite inputs required")
    if infer(term, macros=macros) != "sequence": raise ValueError("sequence root required")
    t = expanded(term, macros or {})
    if cost(t) > 256: raise ValueError("expanded syntax budget exceeded")
    N = len(inputs[0]); budget = Budget(operations); cache = {}
    def run(p):
        key = canonical(p)
        if key in cache: return cache[key]
        o = p[0]
        if o == "input": out = list(inputs[p[1]])
        elif o == "tab": out = [scalar(p[1], {"n": n, "N": N}, budget) for n in range(1, N + 1)]
        elif o == "apply":
            M = matrix(p[1], N, budget, inverse_max); x = run(p[2]); budget.step(N * N)
            out = [sum((a * b for a, b in zip(row, x)), Q(0)) for row in M]
        elif o == "pair":
            x, y = run(p[2]), run(p[3]); out = []
            for n in range(1, N + 1):
                total = Q(0)
                for i in range(1, N + 1):
                    for j in range(1, N + 1):
                        if x[i - 1] and y[j - 1]:
                            budget.step(2)
                            total += scalar(p[1], {"n": n, "i": i, "j": j, "N": N}, budget) * x[i - 1] * y[j - 1]
                out.append(total)
        elif o == "scale":
            a = scalar(p[1], {"N": N}, budget); budget.step(N); out = [a * b for b in run(p[2])]
        elif o == "norm2":
            budget.step(3 * N); out = [norm2(x) for x in run(p[1])]
        else:
            a, b = run(p[1]), run(p[2]); budget.step(N)
            out = [x + y if o == "add" else x * y for x, y in zip(a, b)]
        cache[key] = out
        return out
    output = run(t)
    return output, budget.used


def polynomial_certificate(term, macros=None):
    """Existing exact-arithmetic proof backend, restricted to a polynomial sort.

    Arithmetic functions are substituted into a commutative polynomial ring.
    Unsupported sums/maps/conjugations remain unsupported, never disproved.
    """
    t = expanded(term, macros or {})
    def poly(p):
        o = p[0]
        if o == "input": return {(int(p[1] == 0), int(p[1] == 1)): Q(1)}
        if o == "tab" and p[1][0] == "q": return {(0, 0): Q(p[1][1], p[1][2])}
        if o == "scale" and p[1][0] == "q": return {m: Q(p[1][1], p[1][2]) * a for m, a in poly(p[2]).items()}
        if o not in {"add", "point"}: raise ValueError("certificate method unavailable for this sort")
        a, b = poly(p[1]), poly(p[2]); out = dict(a) if o == "add" else {}
        if o == "add":
            for m, x in b.items(): out[m] = out.get(m, Q(0)) + x
        else:
            for m, x in a.items():
                for n, y in b.items():
                    k = (m[0] + n[0], m[1] + n[1]); out[k] = out.get(k, Q(0)) + x * y
        return {m: x for m, x in out.items() if x}
    try:
        result = poly(t)
    except ValueError as e:
        return {"status": "unsupported", "reason": str(e), "imported_theorems": []}
    # Exercise the established finite coefficient backend, in addition to the
    # universal polynomial-ring argument. This sample is corroboration only.
    from exact_arithmetic import add, pointwise, scale, sequence
    def old(p):
        if p[0] == "input": return sequence([Q(2), Q(-3)] if p[1] == 0 else [Q(-5), Q(7)])
        if p[0] == "tab": return sequence([Q(p[1][1], p[1][2])] * 2)
        if p[0] == "scale": return scale(old(p[2]), Q(p[1][1], p[1][2]))
        return (add if p[0] == "add" else pointwise)(old(p[1]), old(p[2]))
    corroboration = old(t)
    expected = [sum((v * x ** a * y ** b for (a, b), v in result.items()), Q(0)) for x, y in [(2, -5), (-3, 7)]]
    if corroboration[1:] != expected: raise ValueError("existing backend disagreement")
    return {"status": "universal_arithmetic_identity_proved", "domain": "all Q(i)-valued arithmetic functions, at every integer coefficient",
            "normal_form": [[a, b, v.numerator, v.denominator] for (a, b), v in sorted(result.items())],
            "method": "commutative polynomial normalization; existing exact_arithmetic.py finite corroboration",
            "imported_theorems": [], "analytic_claim": False}
