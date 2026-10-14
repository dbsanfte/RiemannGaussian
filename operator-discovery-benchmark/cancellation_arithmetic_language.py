"""Compositional signed arithmetic sums compiled to exact finite polynomials.

This is a representation layer, not an arithmetic oracle or a bound theorem.
Every sum uses its stated inclusive endpoints. No index or remainder is clipped.
False guards suppress evaluation (not type checking) of their polynomial body.
"""
from copy import deepcopy
from fractions import Fraction as Q
import hashlib
import json
from math import gcd, isqrt

import grouped_arithmetic_language as L

VERSION = 'signed-arithmetic-sums-v1'
INDEX_BINARY = {'iadd', 'isub', 'imul', 'idiv', 'imod', 'gcd', 'min', 'max'}
COMPARE = {'eq', 'le', 'lt', 'divides'}


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _integer(value, minimum=None):
    if type(value) is not int or minimum is not None and value < minimum:
        raise ValueError('strict integer domain')
    return value


def _rational(value, max_bits=2048):
    if type(value) is not str:
        raise ValueError('canonical rational string required')
    # Check the text before Fraction can allocate a huge decimal/exponent input.
    if len(value) > 2*max_bits + 3:
        raise OverflowError('rational input text budget')
    if not value or any(c not in '-/0123456789' for c in value):
        raise ValueError('rational integer/fraction syntax required')
    answer = Q(value)
    if max(abs(answer.numerator).bit_length(), answer.denominator.bit_length()) > max_bits:
        raise OverflowError('rational coefficient bit budget')
    if str(answer) != value:
        raise ValueError('noncanonical rational')
    return answer


class Compiler:
    def __init__(self, X, horizon, *, max_operations=2000000, max_terms=10000,
                 max_degree=6, max_nodes=2048, max_depth=32,
                 max_integer_bits=256, max_coefficient_bits=2048):
        self.X = _integer(X, 1)
        self.horizon = _integer(horizon, 1)
        for name, value in locals().copy().items():
            if name.startswith('max_'):
                setattr(self, name, _integer(value, 1))
        self.operations = 0
        self.nodes = 0
        self.prime_cache = {}
        self.check_integer(X)
        self.check_integer(horizon)

    def charge(self, count=1):
        self.operations += count
        if self.operations > self.max_operations:
            raise OverflowError('expression work budget')

    def check_integer(self, value):
        _integer(value)
        if abs(value).bit_length() > self.max_integer_bits:
            raise OverflowError('index bit budget')
        return value

    def check_polynomial(self, p):
        if len(p) > self.max_terms:
            raise OverflowError('expression term budget')
        for m, q in p.items():
            if len(m) > self.max_degree:
                raise OverflowError('expression degree budget')
            if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > self.max_coefficient_bits:
                raise OverflowError('expression coefficient bit budget')
        return p

    def infer(self, t, scope, depth=0):
        self.nodes += 1
        self.charge()
        if self.nodes > self.max_nodes or depth > self.max_depth:
            raise OverflowError('expression syntax budget')
        if type(t) is not list or not t or type(t[0]) is not str:
            raise ValueError('expression node')
        op = t[0]
        if op == 'int' and len(t) == 2:
            self.check_integer(t[1])
            return 'index'
        if op == 'v' and len(t) == 2:
            if type(t[1]) is not str or t[1] not in scope:
                raise ValueError('unbound index')
            return 'index'
        if op == 'q' and len(t) == 2:
            self.check_polynomial(L.constant(_rational(t[1], self.max_coefficient_bits)))
            return 'poly'
        if op == 'root' and len(t) == 4:
            _integer(t[2], 0)
            _integer(t[3], 1)
            self.check_integer(t[2]); self.check_integer(t[3])
            if self.infer(t[1], scope, depth + 1) != 'index':
                raise ValueError('root index type')
            return 'index'
        if op == 'scale' and len(t) == 3:
            self.check_polynomial(L.constant(_rational(t[1], self.max_coefficient_bits)))
            if self.infer(t[2], scope, depth + 1) != 'poly':
                raise ValueError('scale polynomial type')
            return 'poly'
        if op == 'sum' and len(t) == 5:
            name = t[1]
            if type(name) is not str or not name.isidentifier() or name in scope:
                raise ValueError('fresh sum binding required')
            if any(self.infer(e, scope, depth + 1) != 'index' for e in t[2:4]):
                raise ValueError('sum endpoint types')
            if self.infer(t[4], scope | {name}, depth + 1) != 'poly':
                raise ValueError('sum polynomial type')
            return 'poly'
        signatures = {**{k: ('index', ['index', 'index']) for k in INDEX_BINARY},
                      **{k: ('bool', ['index', 'index']) for k in COMPARE},
                      'prime': ('bool', ['index']), 'squarefree': ('bool', ['index']),
                      'and': ('bool', ['bool', 'bool']), 'or': ('bool', ['bool', 'bool']),
                      'not': ('bool', ['bool']), 'x': ('poly', ['index']),
                      'embed': ('poly', ['index']), 'ratio': ('poly', ['index', 'index']),
                      'add': ('poly', ['poly', 'poly']), 'mul': ('poly', ['poly', 'poly']),
                      'guard': ('poly', ['bool', 'poly'])}
        if op not in signatures:
            raise ValueError('unknown expression production or arity')
        output, inputs = signatures[op]
        if len(t) != len(inputs) + 1:
            raise ValueError('expression arity')
        for child, want in zip(t[1:], inputs):
            if self.infer(child, scope, depth + 1) != want:
                raise ValueError('expression type mismatch')
        return output

    def prime(self, n):
        if n < 2:
            return False
        if n not in self.prime_cache:
            # Preflight the full trial predicate before any long iteration.
            self.charge(max(0, isqrt(n) - 1))
            self.prime_cache[n] = all(n % d for d in range(2, isqrt(n) + 1))
        return self.prime_cache[n]

    def run(self, t, env):
        self.charge()
        op = t[0]
        if op == 'int': return t[1]
        if op == 'v': return env[t[1]]
        if op == 'q': return L.constant(_rational(t[1], self.max_coefficient_bits))
        if op == 'embed': return self.check_polynomial(L.constant(self.run(t[1], env)))
        if op == 'x':
            n = self.run(t[1], env)
            if not 1 <= n <= self.horizon:
                raise ValueError('sequence index outside declared horizon')
            return L.variable(n)
        if op == 'guard':
            return self.run(t[2], env) if self.run(t[1], env) else {}
        if op == 'and': return self.run(t[1], env) and self.run(t[2], env)
        if op == 'or': return self.run(t[1], env) or self.run(t[2], env)
        if op == 'not': return not self.run(t[1], env)
        if op == 'prime': return self.prime(self.run(t[1], env))
        if op == 'squarefree':
            n = self.run(t[1], env)
            if n < 1: return False
            self.charge(max(0, isqrt(n) - 1))
            return all(n % (d*d) for d in range(2, isqrt(n) + 1))
        if op == 'root':
            n = self.run(t[1], env); a, b = t[2:]
            if n < 0: raise ValueError('nonnegative fractional-power base')
            common = gcd(a, b); a //= common; b //= common
            if a == 0: return 1  # Explicit convention, also at base zero.
            if n in (0, 1): return n
            # Bound exact powers before materializing; no floating roots.
            bits = max(a * n.bit_length(), b * n.bit_length())
            if bits > self.max_integer_bits:
                raise OverflowError('fractional-power bit budget')
            self.charge(bits)
            target = n**a
            lo, hi = 0, 1 << ((target.bit_length() + b - 1)//b)
            while lo + 1 < hi:
                self.charge(b * max(1, hi.bit_length()))
                mid = (lo + hi)//2
                if mid**b <= target: lo = mid
                else: hi = mid
            return self.check_integer(lo)
        if op == 'sum':
            lo, hi = self.run(t[2], env), self.run(t[3], env)
            self.charge(max(0, hi - lo + 1))
            total = {}
            for n in range(lo, hi + 1):
                p = self.run(t[4], dict(env, **{t[1]: n}))
                self.charge(len(total) + len(p))
                total = self.check_polynomial(L.add(total, p))
            return total
        if op == 'scale':
            p = self.run(t[2], env); self.charge(len(p))
            return self.check_polynomial(L.scale(p, _rational(t[1], self.max_coefficient_bits)))
        a, b = self.run(t[1], env), self.run(t[2], env)
        if op == 'ratio':
            if b == 0: raise ValueError('zero rational-weight denominator')
            return self.check_polynomial(L.constant(Q(a, b)))
        if op == 'add':
            self.charge(len(a) + len(b))
            return self.check_polynomial(L.add(a, b))
        if op == 'mul':
            self.charge(len(a)*len(b))
            if max(map(len, a), default=0) + max(map(len, b), default=0) > self.max_degree:
                raise OverflowError('expression product degree')
            return self.check_polynomial(L.mul(a, b, max_terms=self.max_terms,
                                               max_operations=self.max_operations))
        if op == 'eq': return a == b
        if op == 'le': return a <= b
        if op == 'lt': return a < b
        if op == 'divides': return a != 0 and b % a == 0
        if op in ('idiv', 'imod') and b == 0:
            raise ValueError('zero index divisor')
        if op == 'iadd': value = a + b
        elif op == 'isub': value = a - b
        elif op == 'imul':
            if a and b and abs(a).bit_length() + abs(b).bit_length() > self.max_integer_bits + 1:
                raise OverflowError('index multiplication bit preflight')
            value = a * b
        elif op == 'idiv': value = a // b
        elif op == 'imod': value = a % b
        elif op == 'gcd': value = gcd(a, b)
        elif op == 'min': value = min(a, b)
        elif op == 'max': value = max(a, b)
        else: raise ValueError('unknown compiled operation')
        return self.check_integer(value)

    def compile(self, expr, bindings=None):
        bindings = {} if bindings is None else bindings
        if type(bindings) is not dict or any(type(k) is not str or not k.isidentifier()
                                             or k in ('X', 'N') for k in bindings):
            raise ValueError('index binding names')
        for v in bindings.values(): self.check_integer(v)
        env = dict(bindings, X=self.X, N=self.horizon)
        if self.infer(expr, set(env)) != 'poly':
            raise ValueError('polynomial expression required')
        return self.check_polynomial(self.run(expr, env))


def compile_expression(expr, X, horizon, bindings=None, **limits):
    c = Compiler(X, horizon, **limits)
    p = c.compile(expr, bindings)
    return dict(poly=L.dump_poly(p), expression_sha256=digest(expr), version=VERSION,
                X=X, horizon=horizon, operations=c.operations, syntax_nodes=c.nodes,
                coefficient_table_used=False, global_bound_proved=False)


def partition(expr, predicate):
    """Split the body beneath every leading sum; return BOTH exact pieces.

    Predicates may use these leading sum variables. For other tree shapes put
    an explicit guard at the desired scope; unbound names are rejected.
    """
    def guarded(t, condition):
        if type(t) is list and len(t) == 5 and t[0] == 'sum':
            return deepcopy(t[:4]) + [guarded(t[4], condition)]
        return ['guard', deepcopy(condition), deepcopy(t)]
    return [guarded(expr, predicate), guarded(expr, ['not', predicate])]


def polarization(left, right):
    """Exact signed product, retaining both square terms (not an SOS bound)."""
    plus = ['add', deepcopy(left), deepcopy(right)]
    minus = ['add', deepcopy(left), ['scale', '-1', deepcopy(right)]]
    return ['scale', '1/4', ['add', ['mul', plus, deepcopy(plus)],
                            ['scale', '-1', ['mul', minus, deepcopy(minus)]]]]


def enumerate_mixes(atoms, coefficients=('-1', '1'), *, include_products=True,
                    max_candidates=512):
    """Deterministic proposal layer; no fitting, theorem admission, or selection.

    Atoms and coefficient choices are supplied assumptions. Costs/validation
    belong to the compiler; failures must remain failures in the caller archive.
    """
    _integer(max_candidates, 1)
    if type(atoms) is not list or type(include_products) is not bool:
        raise ValueError('mix proposal inputs')
    if type(coefficients) not in (tuple, list):
        raise ValueError('finite coefficient choices required')
    if len(atoms) > max_candidates or len(coefficients) > max_candidates:
        raise OverflowError('mix input count budget')
    count = len(atoms) + len(atoms)*(len(atoms)-1)//2*(len(coefficients)+include_products)
    if count > max_candidates:
        raise OverflowError('mix candidate budget; no silent truncation')
    weights = tuple(str(_rational(c)) for c in coefficients)
    proposed = list(deepcopy(atoms))
    for i, left in enumerate(atoms):
        for right in atoms[i+1:]:
            for w in weights:
                proposed.append(['add', deepcopy(left), ['scale', w, deepcopy(right)]])
            if include_products:
                proposed.append(['mul', deepcopy(left), deepcopy(right)])
            if len(proposed) > max_candidates:
                raise OverflowError('mix candidate budget; no silent truncation')
    if len(proposed) > max_candidates:
        raise OverflowError('mix candidate budget')
    unique = {digest(t): t for t in proposed}
    return [dict(id=k, expr=unique[k]) for k in sorted(unique)]
