"""Unfrozen exact signed arithmetic AST and complete finite response clients.

Actual mu uses complete divisor inversion, not a prime oracle. Liouville uses
the square lift mu*1_squares. No coefficient distribution bound is assumed.
Every public outcome is available/missing/invalid; available payloads are JSON
serializable. Exhaustion never publishes a partial sum. Formal logarithms and
complex characters are explicitly unsupported in this initial rational core.
"""

from dataclasses import dataclass
from fractions import Fraction
from math import gcd
import hashlib
import json

from detector_safe_evaluation import EvaluationResult, Status, rational_ceiling


VERSION = 'exact-signed-arithmetic-ast-v1-unfrozen'


@dataclass(frozen=True)
class WorkBudget:
    max_operations: int = 5000000
    max_cells: int = 2000000
    max_bits: int = 1000000
    max_nodes: int = 1024


@dataclass(frozen=True)
class SeqExpr:
    op: str
    args: tuple = ()
    params: tuple = ()

    def to_dict(self):
        return {'op': self.op, 'args': [node.to_dict() for node in self.args],
                'params': dict(self.params)}


def expr(op, *args, **params):
    return SeqExpr(op, tuple(_node(arg) for arg in args),
                   tuple(sorted((key, str(value) if isinstance(value, Fraction) else value)
                                for key, value in params.items())))


def _node(node):
    if isinstance(node, SeqExpr):
        return node
    if not isinstance(node, dict) or set(node) != {'op', 'args', 'params'}:
        raise ValueError('AST requires exactly op, args and params')
    if not isinstance(node['args'], (list, tuple)) or not isinstance(node['params'], dict):
        raise ValueError('AST args/params have invalid types')
    return expr(node['op'], *node['args'], **node['params'])


def json_exact(value):
    if isinstance(value, Fraction):
        return int(value) if value.denominator == 1 else str(value)
    if isinstance(value, dict):
        return {key: json_exact(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_exact(item) for item in value]
    return value


def _digest(value):
    return hashlib.sha256(json.dumps(json_exact(value), sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def _rational(value):
    if isinstance(value, (bool, float)):
        raise ValueError('exact rational input required; floats/bools are invalid')
    return Fraction(value)


def _integer(value, minimum=0):
    if type(value) is not int or value < minimum:
        raise ValueError(f'integer >= {minimum} required')
    return value


class _Unavailable(Exception):
    def __init__(self, reason):
        self.reason = reason


class _Meter:
    def __init__(self, budget):
        if not isinstance(budget, WorkBudget):
            raise ValueError('WorkBudget required')
        for value in (budget.max_operations, budget.max_cells, budget.max_bits, budget.max_nodes):
            _integer(value, 1)
        self.budget, self.operations, self.cells, self.nodes, self.peak_bits = budget, 0, 0, 0, 0

    def work(self, count=1):
        self.operations += count
        if self.operations > self.budget.max_operations:
            raise _Unavailable('operation_budget_exhausted')

    def array(self, length):
        self.cells += length
        if self.cells > self.budget.max_cells:
            raise _Unavailable('cell_budget_exhausted')
        self.work(length)
        return [0] * length

    def value(self, value):
        bits = (abs(value.numerator).bit_length() + value.denominator.bit_length()
                if isinstance(value, Fraction) else abs(value).bit_length())
        self.peak_bits = max(self.peak_bits, bits)
        if bits > self.budget.max_bits:
            raise _Unavailable('coefficient_bit_budget_exhausted')
        return value

    def record(self):
        return {'operations': self.operations, 'allocated_cells': self.cells,
                'evaluated_nodes': self.nodes, 'peak_coefficient_bits': self.peak_bits,
                'accounting': 'charged array initialization, arithmetic/index updates, and support scans; Python object overhead is not a byte-level memory measure',
                'limits': {'operations': self.budget.max_operations,
                           'cells': self.budget.max_cells, 'bits': self.budget.max_bits,
                           'nodes': self.budget.max_nodes}}


def _root(n, k, meter):
    _integer(n); _integer(k, 1)
    meter.work()
    if n < 2 or k == 1:
        return meter.value(n)
    if k >= n.bit_length():
        return 1
    lo, hi = 0, n + 1
    while hi - lo > 1:
        meter.work(k)
        mid = (lo + hi) // 2
        power = meter.value(mid ** k)
        if power <= n:
            lo = mid
        else:
            hi = mid
    return meter.value(lo)


def _ceil(n, power, meter):
    meter.work()
    result = rational_ceiling(n, power, bit_budget=meter.budget.max_bits)
    if result.status is Status.MISSING:
        raise _Unavailable(result.reason)
    if not result.available:
        raise ValueError(result.reason)
    return meter.value(result.value)


class _Evaluator:
    def __init__(self, meter):
        self.meter, self.cache, self.used_ops = meter, {}, set()

    def convolution(self, left, right, N):
        out = self.meter.array(N + 1)
        support_left = [(i, value) for i, value in enumerate(left) if i and value]
        support_right = [(j, value) for j, value in enumerate(right) if j and value]
        self.meter.work(len(left) + len(right))
        for i, a in support_left:
            for j, b in support_right:
                self.meter.work()
                n = i * j
                if n > N:
                    break
                out[n] = self.meter.value(out[n] + a * b)
        return out

    def mu(self, N):
        values = self.meter.array(N + 1)
        if N:
            values[1] = 1
        # All proper divisor contributions reach n before iteration d=n.
        for d in range(1, N + 1):
            for n in range(2 * d, N + 1, d):
                self.meter.work()
                values[n] = self.meter.value(values[n] - values[d])
        return values

    def evaluate(self, node, N):
        _integer(N)
        key = (_digest(node.to_dict()), N)
        if key in self.cache:
            return self.cache[key]
        self.meter.nodes += 1
        if self.meter.nodes > self.meter.budget.max_nodes:
            raise _Unavailable('node_budget_exhausted')
        op, args, params = node.op, node.args, dict(node.params)
        self.used_ops.add(op)
        arities = {'one': 0, 'unit': 0, 'mu': 0, 'liouville': 0,
                   'scale': 1, 'prefix': 1, 'shift': 1, 'dilate': 1,
                   'floor_index': 1, 'root_index': 1, 'truncate': 1,
                   'coprime_mask': 1, 'residue_mask': 1, 'normalize': 1,
                   'convolution': 2, 'product': 2}
        if op == 'add':
            if not args or params:
                raise ValueError('add requires children and no parameters')
        elif op not in arities or len(args) != arities[op]:
            raise ValueError('unsupported operation or wrong argument count')
        expected_params = {'scale': {'weight'}, 'shift': {'offset'}, 'dilate': {'factor'},
                           'floor_index': {'divisor'}, 'root_index': {'order'},
                           'truncate': {'cutoff'}, 'coprime_mask': {'modulus'},
                           'residue_mask': {'modulus', 'residue'}, 'normalize': {'power'}}
        if set(params) != expected_params.get(op, set()):
            raise ValueError('unexpected or missing operation parameters')
        if op == 'mu':
            out = self.mu(N)
        elif op in ('one', 'unit'):
            out = self.meter.array(N + 1)
            if op == 'one':
                self.meter.work(N)
                value = self.meter.value(1)
                for n in range(1, N + 1):
                    out[n] = value
            elif N:
                out[1] = self.meter.value(1)
        elif op == 'liouville':
            mu = self.evaluate(expr('mu'), N)
            out = self.meter.array(N + 1)
            for d in range(1, _root(N, 2, self.meter) + 1):
                square = d * d
                for m in range(1, N // square + 1):
                    self.meter.work()
                    out[square * m] = self.meter.value(out[square * m] + mu[m])
        elif op in ('shift', 'dilate', 'floor_index', 'root_index'):
            if op == 'shift':
                offset = params['offset']
                if type(offset) is not int:
                    raise ValueError('integer shift required')
                mapping = lambda n: max(0, n + offset)
                horizon = max(0, N + offset)
            elif op == 'dilate':
                factor = _integer(params['factor'], 1)
                mapping, horizon = lambda n: n * factor, N * factor
            elif op == 'floor_index':
                divisor = _integer(params['divisor'], 1)
                mapping, horizon = lambda n: n // divisor, N // divisor
            else:
                order = _integer(params['order'], 1)
                mapping = lambda n: _root(n, order, self.meter)
                horizon = _root(N, order, self.meter)
            child = self.evaluate(args[0], horizon)
            out = self.meter.array(N + 1)
            for n in range(1, N + 1):
                self.meter.work()
                out[n] = child[mapping(n)]
        elif op == 'truncate':
            cutoff = _integer(params['cutoff'])
            child = self.evaluate(args[0], min(cutoff, N))
            out = self.meter.array(N + 1)
            out[:len(child)] = child
        elif op == 'convolution':
            out = self.convolution(self.evaluate(args[0], N), self.evaluate(args[1], N), N)
        elif op == 'add':
            out = self.meter.array(N + 1)
            for child_node in args:
                child = self.evaluate(child_node, N)
                for n in range(1, N + 1):
                    self.meter.work()
                    out[n] = self.meter.value(out[n] + child[n])
        else:
            child = self.evaluate(args[0], N)
            out = self.meter.array(N + 1)
            if op == 'product':
                right = self.evaluate(args[1], N)
            elif op == 'scale':
                weight = self.meter.value(_rational(params['weight']))
            elif op in ('coprime_mask', 'residue_mask'):
                modulus = _integer(params['modulus'], 1)
                if op == 'residue_mask':
                    residue = _integer(params['residue'])
                    if residue >= modulus:
                        raise ValueError('canonical residue in [0,modulus) required')
            elif op == 'normalize':
                power = _rational(params['power'])
                if power < 0:
                    raise ValueError('nonnegative normalizing power required')
            total = 0
            for n in range(1, N + 1):
                self.meter.work()
                if op == 'product':
                    value = child[n] * right[n]
                elif op == 'scale':
                    value = weight * child[n]
                elif op == 'prefix':
                    total += child[n]
                    value = total
                elif op == 'coprime_mask':
                    value = child[n] if gcd(n, modulus) == 1 else 0
                elif op == 'residue_mask':
                    value = child[n] if n % modulus == residue else 0
                else:
                    value = Fraction(child[n]) / _ceil(n, power, self.meter)
                out[n] = self.meter.value(value)
        self.cache[key] = out
        return out

    def provenance(self):
        return {'grammar_version': VERSION, 'operations_used': sorted(self.used_ops),
                'mu_origin': 'complete_proper_divisor_inversion' if 'mu' in self.used_ops else None,
                'liouville_origin': 'mu_convolved_with_square_indicator' if 'liouville' in self.used_ops else None,
                'prime_or_factor_oracle_used': False, 'zero_index_convention': 0,
                'formal_logarithms_supported': False,
                'global_actual_signed_bound_proved': False}


def _run(client, budget):
    meter = None
    try:
        meter = _Meter(budget or WorkBudget())
        evaluator = _Evaluator(meter)
        payload = client(evaluator)
        payload.update({'cost': meter.record(), 'provenance': evaluator.provenance()})
        return EvaluationResult(Status.AVAILABLE, json_exact(payload))
    except _Unavailable as exc:
        return EvaluationResult(Status.MISSING, reason=exc.reason,
                                details={'cost': meter.record() if meter else None})
    except (MemoryError, OverflowError, RecursionError) as exc:
        return EvaluationResult(Status.MISSING, reason='native_resource_exhaustion',
                                details={'error': str(exc), 'cost': meter.record() if meter else None})
    except (ValueError, TypeError, KeyError, ZeroDivisionError) as exc:
        return EvaluationResult(Status.INVALID, reason='invalid_arithmetic_expression',
                                details={'error': str(exc)})


def evaluate(node, N, *, budget=None):
    def client(evaluator):
        expression = _node(node)
        return {'expression': expression.to_dict(), 'horizon': N,
                'coefficients': evaluator.evaluate(expression, N)}
    return _run(client, budget)


def complete_mobius(N, *, budget=None):
    return evaluate(expr('mu'), N, budget=budget)


def floor_root(n, order, *, budget=None):
    return _run(lambda evaluator: {'root': _root(n, order, evaluator.meter),
                                  'base': n, 'order': order}, budget)


def ceil_power(n, power, *, budget=None):
    return _run(lambda evaluator: {'ceiling': _ceil(n, power, evaluator.meter),
                                  'base': n, 'power': str(_rational(power))}, budget)


def mixed_moment(left, right, X, *, weight=None, child=False, budget=None):
    """Complete signed inner product on [X,2X), or [2X,4X) when child."""
    def client(evaluator):
        _integer(X, 1)
        if type(child) is not bool:
            raise ValueError('boolean child flag required')
        start, stop = (2 * X, 4 * X) if child else (X, 2 * X)
        a = evaluator.evaluate(_node(left), stop - 1)
        b = evaluator.evaluate(_node(right), stop - 1)
        w = evaluator.evaluate(_node(weight), stop - 1) if weight is not None else None
        total = 0
        for n in range(start, stop):
            evaluator.meter.work()
            total = evaluator.meter.value(total + a[n] * b[n] * (w[n] if w is not None else 1))
        return {'X': X, 'interval': [start, stop], 'signed_sum': total,
                'term_count': stop - start, 'complete_domain': True,
                'all_signed_products_retained': True}
    return _run(client, budget)


def coupled_response(X, *, budget=None):
    """Full actual k=2 shared-cutoff response, including both cross blocks."""
    def client(evaluator):
        _integer(X, 1)
        N = 4 * X - 1
        u = _root(N, 2, evaluator.meter)
        mu = expr('mu')
        small = expr('truncate', mu, cutoff=u)
        F1 = evaluator.evaluate(expr('prefix', small), N)
        F2 = evaluator.evaluate(expr('prefix', expr('convolution',
            expr('convolution', small, small), expr('one'))), N)
        M = evaluator.evaluate(expr('prefix', mu), N)
        moments = {}
        for name, a, b in [('actual', M, M), ('F1', F1, F1), ('F2', F2, F2),
                           ('cross', F1, F2)]:
            parent, child = 0, 0
            for n in range(X, 4 * X):
                evaluator.meter.work()
                value = evaluator.meter.value(a[n] * b[n])
                if n < 2 * X:
                    parent = evaluator.meter.value(parent + value)
                else:
                    child = evaluator.meter.value(child + value)
            moments[name] = {'parent': parent, 'child': child, 'defect': child - 4 * parent}
        full = moments['actual']['defect']
        credit = 4 * moments['F1']['defect']
        residual = moments['F2']['defect'] - 4 * moments['cross']['defect']
        recovered = all(M[n] == 2 * F1[n] - F2[n] for n in range(N + 1))
        evaluator.meter.work(N + 1)
        return {'X': X, 'cutoff': u, 'shared_cutoff': True,
            'strict_support_condition': (u + 1) ** 2 > N,
            'energy': moments['actual']['parent'], 'child_energy': moments['actual']['child'],
            'signed_defect': full, 'moments': moments,
            'negative_low_prefix_credit': credit, 'coupled_residual': residual,
            'reconstructed_defect': credit + residual,
            'identity_residual': full - credit - residual,
            'all_prefix_coefficients_recovered': recovered,
            'actual_prefix_sha256': _digest(M),
            'component_inverse_prefix_through': u, 'actual_target_inverse_through': N,
            'all_terms_and_cross_terms_retained': True,
            'representation_weight_l1': 3,
            'complete_domain': [X, 4 * X], 'moving_cutoff_between_calls': True,
            'global_actual_signed_bound_proved': False}
    return _run(client, budget)


def liouville_floor_sum(x, *, budget=None):
    """Actual signed divisor-weighted calibration response, without oracle target."""
    def client(evaluator):
        _integer(x, 1)
        values = evaluator.evaluate(expr('liouville'), x)
        signed, unsigned = 0, 0
        for d in range(1, x + 1):
            evaluator.meter.work()
            term = evaluator.meter.value(values[d] * (x // d))
            signed = evaluator.meter.value(signed + term)
            unsigned = evaluator.meter.value(unsigned + abs(term))
        return {'x': x, 'signed_sum': signed, 'unsigned_charge': unsigned,
                'term_count': x, 'complete_domain': True,
                'filtered_calibration_not_mertens_target': True}
    return _run(client, budget)
