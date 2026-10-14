"""Hash-free exact scalar evaluation of squared arithmetic-state potentials.

This is a finite research evaluator. Nonnegative potential weights preserve
the complete target energy; finite evaluations supply no uniform estimate.
"""
from copy import deepcopy
from fractions import Fraction as Q
from math import gcd, isqrt, isfinite
import time

INDEX_BINARY = {'iadd', 'isub', 'imul', 'idiv', 'imod', 'gcd', 'min', 'max'}
COMPARE = {'eq', 'le', 'lt', 'divides'}
SIGNATURES = {**{k: ('index', ('index', 'index')) for k in INDEX_BINARY},
              **{k: ('bool', ('index', 'index')) for k in COMPARE},
              'prime': ('bool', ('index',)), 'squarefree': ('bool', ('index',)),
              'and': ('bool', ('bool', 'bool')), 'or': ('bool', ('bool', 'bool')),
              'not': ('bool', ('bool',)), 'x': ('scalar', ('index',)),
              'embed': ('scalar', ('index',)), 'ratio': ('scalar', ('index', 'index')),
              'add': ('scalar', ('scalar', 'scalar')), 'mul': ('scalar', ('scalar', 'scalar')),
              'guard': ('scalar', ('bool', 'scalar'))}


class Meter:
    def __init__(self, max_operations, *, deadline=None, max_cells=6000000, max_bits=4096):
        if (type(max_operations) is not int or max_operations < 1
                or type(max_cells) is not int or not 1 <= max_cells <= 6000000
                or type(max_bits) is not int or not 1 <= max_bits <= 4096
                or deadline is not None and (type(deadline) not in (int, float) or not isfinite(deadline))):
            raise ValueError('bounded shared exact evaluator meter')
        self.max_operations = max_operations; self.deadline = deadline
        self.max_cells = max_cells; self.max_bits = max_bits
        self.operations = 0; self.peak_live_cells = 0; self.maximum_rational_bits = 0

    def charge(self, n=1):
        if type(n) is not int or n < 0:
            raise ValueError('nonnegative exact work charge')
        if n > self.max_operations - self.operations:
            raise OverflowError('shared exact evaluator operation cap')
        self.operations += n
        if self.deadline is not None and time.monotonic() > self.deadline:
            raise TimeoutError('shared exact evaluator deadline')

    def live(self, cells):
        self.charge()
        if type(cells) is not int or cells < 0:
            raise ValueError('nonnegative live scalar cells')
        self.peak_live_cells = max(self.peak_live_cells, cells)
        if cells > self.max_cells:
            raise OverflowError('shared exact evaluator live cell cap')

    def number(self, value):
        self.charge()
        if type(value) not in (int, Q):
            raise ValueError('exact integer or rational required')
        bits = (abs(value).bit_length() if type(value) is int else
                max(abs(value.numerator).bit_length(), value.denominator.bit_length()))
        self.maximum_rational_bits = max(self.maximum_rational_bits, bits)
        if bits > self.max_bits:
            raise OverflowError('shared exact evaluator number bit cap')
        return value

    def counts(self):
        return dict(operations=self.operations, peak_live_cells=self.peak_live_cells,
                    maximum_rational_bits=self.maximum_rational_bits)


def _rational(text, meter):
    if type(text) is not str:
        raise ValueError('canonical rational string required')
    meter.charge(len(text) // 32 + 1)
    parts = text.split('/')
    if (not text or len(parts) > 2
            or any(not p or not p.lstrip('-').isdigit() or p.startswith('--') for p in parts)
            or any(len(p.lstrip('-')) > int(meter.max_bits * .30103) + 2 for p in parts)):
        raise ValueError('bounded rational integer/fraction syntax')
    integers = [meter.number(int(p)) for p in parts]
    if len(integers) == 2 and integers[1] <= 0:
        raise ValueError('positive rational denominator')
    value = meter.number(Q(*integers))
    if str(value) != text:
        raise ValueError('canonical reduced rational required')
    return value


def validate_candidate(candidate, meter):
    if type(candidate) is not dict or set(candidate) != {'states'}:
        raise ValueError('exact states-only candidate schema')
    states = candidate['states']
    if type(states) is not list or len(states) > 2:
        raise ValueError('zero to two weighted arithmetic states')
    count = 0

    def infer(node, scope, depth=0):
        nonlocal count
        meter.charge(); count += 1
        if count > 256 or depth > 24:
            raise OverflowError('candidate syntax node/depth cap')
        if type(node) is not list or not node or type(node[0]) is not str:
            raise ValueError('arithmetic syntax node')
        op = node[0]
        meter.charge(len(op) // 32 + 1)
        if op == 'int' and len(node) == 2:
            if type(node[1]) is not int:
                raise ValueError('strict index integer')
            meter.number(node[1]); return 'index'
        if op == 'v' and len(node) == 2:
            if type(node[1]) is not str:
                raise ValueError('index variable name')
            meter.charge(len(node[1]) // 32 + 1)
            if node[1] not in scope:
                raise ValueError('bound X,t or lexical index variable required')
            return 'index'
        if op == 'q' and len(node) == 2:
            _rational(node[1], meter); return 'scalar'
        if op == 'root' and len(node) == 4:
            a, b = node[2:]
            if type(a) is not int or a < 0 or type(b) is not int or b < 1:
                raise ValueError('nonnegative rational root exponent')
            meter.number(a); meter.number(b)
            if infer(node[1], scope, depth + 1) != 'index':
                raise ValueError('root index input')
            return 'index'
        if op == 'scale' and len(node) == 3:
            _rational(node[1], meter)
            if infer(node[2], scope, depth + 1) != 'scalar':
                raise ValueError('scaled scalar input')
            return 'scalar'
        if op == 'sum' and len(node) == 5:
            name = node[1]
            if type(name) is not str:
                raise ValueError('lexical sum variable')
            meter.charge(len(name) // 32 + 1)
            if not name.isidentifier() or name in scope or name == 'N':
                raise ValueError('fresh lexical sum binding required')
            if (infer(node[2], scope, depth + 1) != 'index'
                    or infer(node[3], scope, depth + 1) != 'index'
                    or infer(node[4], scope | {name}, depth + 1) != 'scalar'):
                raise ValueError('inclusive sum endpoint/body types')
            return 'scalar'
        if op not in SIGNATURES:
            raise ValueError('supported legacy arithmetic production required')
        output, inputs = SIGNATURES[op]
        if len(node) != len(inputs) + 1:
            raise ValueError('arithmetic production arity')
        for child, expected in zip(node[1:], inputs):
            if infer(child, scope, depth + 1) != expected:
                raise ValueError('arithmetic production type mismatch')
        return output

    for state in states:
        meter.charge()
        if type(state) is not dict or set(state) != {'weight', 'tree'}:
            raise ValueError('weight/tree state schema')
        if _rational(state['weight'], meter) < 0:
            raise ValueError('nonnegative potential weight required')
        if infer(state['tree'], {'X', 't'}) != 'scalar':
            raise ValueError('arithmetic scalar state required')
    meter.live(8 * count + 8)
    return count


def mobius(horizon, meter):
    if type(horizon) is not int or horizon < 1:
        raise ValueError('positive complete source horizon')
    meter.number(horizon); meter.charge(horizon + 1); meter.live(horizon + 1)
    values = [0] * (horizon + 1); values[1] = 1
    # Divisor inversion of sum_{d|n} mu(d)=1_{n=1}, including EVERY
    # proper divisor. Increasing d ensures its own value is already final.
    for d in range(1, horizon + 1):
        meter.charge()
        for multiple in range(2 * d, horizon + 1, d):
            meter.charge(); values[multiple] = meter.number(values[multiple] - values[d])
    return values


def control_source(name, mu, meter):
    if name not in ('mu', 'one', 'partial_prime_2'):
        raise ValueError('declared arithmetic diagnostic source')
    if type(mu) is not list or len(mu) < 2 or mu[0] != 0:
        raise ValueError('complete index-zero-padded mu source')
    meter.charge(len(mu)); meter.live(2 * len(mu)); result = [0]
    for n, value in enumerate(mu[1:], 1):
        meter.number(value)
        if type(value) is not int or value not in (-1, 0, 1):
            raise ValueError('actual complete mu coefficients')
        if name == 'mu':
            result.append(value)
        elif name == 'one':
            result.append(1)
        else:
            meter.charge(); result.append(meter.number(value * value * (-1 if n % 2 == 0 else 1)))
    return result


class Evaluator:
    def __init__(self, values, meter):
        self.meter = meter
        if type(values) is not list or len(values) < 2:
            raise ValueError('complete positive-index exact scalar source')
        meter.charge(len(values)); meter.live(4 * len(values))
        self.values = tuple(Q(meter.number(value)) for value in values)
        self.horizon = len(values) - 1
        self.cells = 4 * len(values); self.syntax = {}; self.dependencies = {}
        self.memo = {}; self.sums = {}; self.primes = {}; self.squarefrees = {}; self.measures = {}
        self.prefix = [Q(0)]; self.energy = [Q(0)]
        for value in self.values[1:]:
            meter.charge(); total = meter.number(self.prefix[-1] + value)
            square = meter.number(total * total)
            self.prefix.append(total); self.energy.append(meter.number(self.energy[-1] + square))
        self._live()

    def _live(self, extra=0):
        self.meter.live(self.cells + extra)

    def _freeze(self, node):
        self.meter.charge()
        frozen = tuple(self._freeze(child) if type(child) is list else child for child in node)
        if frozen not in self.syntax:
            self._live(len(frozen) + 4)
            self.syntax[frozen] = frozen; self.cells += len(frozen) + 4
        return self.syntax[frozen]

    def _free(self, node):
        self.meter.charge()
        if node in self.dependencies:
            return self.dependencies[node]
        op = node[0]
        if op == 'v':
            free = frozenset([node[1]])
        elif op in ('int', 'q'):
            free = frozenset()
        elif op == 'sum':
            free = self._free(node[2]) | self._free(node[3]) | (self._free(node[4]) - {node[1]})
        else:
            free = frozenset().union(*(self._free(child) for child in node[1:] if type(child) is tuple))
        self._live(2 * len(free) + 2)
        self.dependencies[node] = free; self.cells += 2 * len(free) + 2
        return free

    def _environment(self, names, env):
        self.meter.charge(len(names) + 1)
        return tuple((name, env[name]) for name in sorted(names))

    def _predicate(self, n, squarefree=False):
        cache = self.squarefrees if squarefree else self.primes
        if n in cache:
            return cache[n]
        if n < (1 if squarefree else 2):
            value = False
        else:
            end = isqrt(n); self.meter.charge(max(0, end - 1))
            value = all(n % (d * d if squarefree else d) for d in range(2, end + 1))
        self._live(3); cache[n] = value; self.cells += 3
        return value

    def _run(self, node, env):
        self.meter.charge()
        environment = self._environment(self._free(node), env); key = (node, environment)
        if key in self.memo:
            return self.memo[key]
        op = node[0]
        if op == 'int':
            value = node[1]
        elif op == 'v':
            value = env[node[1]]
        elif op == 'q':
            value = _rational(node[1], self.meter)
        elif op == 'embed':
            value = Q(self._run(node[1], env))
        elif op == 'x':
            n = self._run(node[1], env)
            if not 1 <= n <= self.horizon:
                raise ValueError('source index outside complete declared horizon')
            value = self.values[n]
        elif op == 'guard':
            value = self._run(node[2], env) if self._run(node[1], env) else Q(0)
        elif op == 'and':
            value = self._run(node[1], env) and self._run(node[2], env)
        elif op == 'or':
            value = self._run(node[1], env) or self._run(node[2], env)
        elif op == 'not':
            value = not self._run(node[1], env)
        elif op in ('prime', 'squarefree'):
            value = self._predicate(self._run(node[1], env), op == 'squarefree')
        elif op == 'root':
            n = self._run(node[1], env); a, b = node[2:]
            if n < 0:
                raise ValueError('nonnegative fractional-power base')
            common = gcd(a, b); a //= common; b //= common
            if a == 0:
                value = 1
            elif n in (0, 1):
                value = n
            else:
                bits = max(a * n.bit_length(), b * n.bit_length())
                if bits > self.meter.max_bits:
                    raise OverflowError('fractional-power integer bit preflight')
                self.meter.charge(bits); target = n ** a
                lo = 0; hi = 1 << ((target.bit_length() + b - 1) // b)
                while lo + 1 < hi:
                    self.meter.charge(b * max(1, hi.bit_length()))
                    mid = (lo + hi) // 2
                    if mid ** b <= target:
                        lo = mid
                    else:
                        hi = mid
                value = self.meter.number(lo)
        elif op == 'sum':
            lo = self._run(node[2], env); hi = self._run(node[3], env)
            if hi < lo:
                value = Q(0)
            else:
                name = node[1]; body = node[4]
                fixed = self._environment(self._free(body) - {name}, env)
                sum_key = (name, body, lo, fixed)
                if sum_key not in self.sums:
                    self._live(6 + 2 * len(fixed))
                    self.sums[sum_key] = [Q(0)]; self.cells += 6 + 2 * len(fixed)
                totals = self.sums[sum_key]
                start = lo + len(totals) - 1
                self.meter.charge(max(0, hi - start + 1))
                for n in range(start, hi + 1):
                    self.meter.number(n)
                    child = self._run(body, dict(env, **{name: n}))
                    total = self.meter.number(totals[-1] + child)
                    self._live(1); totals.append(total); self.cells += 1
                value = totals[hi - lo + 1]
        elif op == 'scale':
            coefficient = _rational(node[1], self.meter)
            value = self.meter.number(coefficient * self._run(node[2], env))
        else:
            a = self._run(node[1], env); b = self._run(node[2], env)
            if op == 'ratio':
                if b == 0:
                    raise ValueError('zero rational-weight denominator')
                value = self.meter.number(Q(a, b))
            elif op == 'add':
                value = self.meter.number(a + b)
            elif op == 'mul':
                value = self.meter.number(a * b)
            elif op == 'eq':
                value = a == b
            elif op == 'le':
                value = a <= b
            elif op == 'lt':
                value = a < b
            elif op == 'divides':
                value = a != 0 and b % a == 0
            else:
                if op in ('idiv', 'imod') and b == 0:
                    raise ValueError('zero index divisor')
                if op == 'iadd':
                    value = a + b
                elif op == 'isub':
                    value = a - b
                elif op == 'imul':
                    if a and b and abs(a).bit_length() + abs(b).bit_length() > self.meter.max_bits + 1:
                        raise OverflowError('index multiplication integer bit preflight')
                    value = a * b
                elif op == 'idiv':
                    value = a // b
                elif op == 'imod':
                    value = a % b
                elif op == 'gcd':
                    value = gcd(a, b)
                elif op == 'min':
                    value = min(a, b)
                else:
                    value = max(a, b)
                value = self.meter.number(value)
        if type(value) in (int, Q):
            self.meter.number(value)
        cells = 5 + 2 * len(environment)
        self._live(cells); self.memo[key] = value; self.cells += cells
        return value

    def measure(self, candidate, X):
        if type(X) is not int or X < 1:
            raise ValueError('positive integer scale')
        self.meter.number(X)
        if 2 * X - 1 > self.horizon:
            raise ValueError('complete parent dyadic interval source required')
        nodes = validate_candidate(candidate, self.meter); self._live(8 * nodes + 8)
        states = tuple((state['weight'], self._freeze(state['tree'])) for state in candidate['states'])
        key = (states, X)
        if key in self.measures:
            return dict(self.measures[key])
        self.meter.charge(); denominator = self.meter.number(X * X)
        normalization = self.meter.number(Q(1, denominator))
        energy_sum = self.meter.number(self.energy[2 * X - 1] - self.energy[X - 1])
        energy = self.meter.number(normalization * energy_sum)
        potential = Q(0)
        weights = [_rational(weight, self.meter) for weight, _ in states]
        for t in range(X, 2 * X):
            self.meter.charge()
            for weight, (_, tree) in zip(weights, states):
                value = self._run(tree, {'X': X, 't': t})
                square = self.meter.number(value * value)
                term = self.meter.number(weight * square)
                potential = self.meter.number(potential + term)
        potential = self.meter.number(normalization * potential)
        total = self.meter.number(energy + potential)
        result = dict(X=X, E=str(energy), V=str(potential), W=str(total))
        cells = 8 + sum(len(result[k]) // 8 + 1 for k in ('E', 'V', 'W'))
        self._live(cells); self.measures[key] = result; self.cells += cells
        return dict(result)

    def case(self, candidate, X):
        if type(X) is not int or X < 1:
            raise ValueError('positive integer scale')
        self.meter.number(X)
        if 4 * X - 1 > self.horizon:
            raise ValueError('complete parent and child dyadic source required')
        parent = self.measure(candidate, X); child = self.measure(candidate, 2 * X)
        self.meter.charge((len(child['W']) + len(parent['W'])) // 32 + 1)
        innovation = self.meter.number(Q(child['W']) - Q(parent['W']))
        return dict(X=X, parent=parent, child=child, innovation=str(innovation))


def potential_tree(candidate):
    """Legacy AST for the ENTIRE potential, preserving cross terms in U²."""
    body = ['q', '0']
    for state in candidate['states']:
        tree = state['tree']
        term = ['scale', state['weight'], ['mul', deepcopy(tree), deepcopy(tree)]]
        body = ['add', body, term]
    return ['mul', ['ratio', ['int', 1], ['imul', ['v', 'X'], ['v', 'X']]],
            ['sum', 't', ['v', 'X'], ['isub', ['imul', ['int', 2], ['v', 'X']], ['int', 1]], body]]
