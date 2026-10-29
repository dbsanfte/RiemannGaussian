"""Paid materialized Boolean counter with homogeneous integer jet arithmetic.

The source layout is constructed by the existing pinned source constructor.
This module caches original truth tables and head fibres. It never calls a
full-assignment diagnostic. Integer jets carry the DECLARED denominator degree,
so every counter accumulator uses a power of one acquired source denominator.
This is an executable research implementation, not a Lean machine-clock proof.
"""
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import combinations, product
from math import comb, lcm
from pathlib import Path
import importlib.util
import sys

ROOT = Path('/home/dbsanfte/riemann/formal')
FROZEN = ROOT / 'docs/research-evidence/semiprime-shared-counter-20261026'
SOURCE = ROOT / 'docs/research-evidence/semiprime-executable-counter-20261027'


def load_file(name, path):
    if name in sys.modules:
        if Path(sys.modules[name].__file__).resolve() != path.resolve():
            raise ImportError('conflicting module: ' + name)
        return sys.modules[name]
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def reference():
    return load_file('_paid_reference_counter', FROZEN / 'shared_counter.py')


@dataclass(frozen=True)
class Jet:
    coefficients: tuple
    degree: int


@dataclass
class Meter:
    counts: dict = field(default_factory=dict)
    max_integer_bits: int = 0
    max_declared_degree: int = 0

    def inc(self, name, amount=1):
        self.counts[name] = self.counts.get(name, 0) + amount

    def integer(self, value):
        self.max_integer_bits = max(self.max_integer_bits, abs(value).bit_length())
        return value


class HomogeneousJets:
    def __init__(self, precision, denominator, total_degree, meter):
        if precision < 1 or denominator < 1 or total_degree < 0:
            raise ValueError('invalid jet dimensions')
        self.J, self.denominator, self.total_degree = precision, denominator, total_degree
        self.meter = meter
        self.powers = [1]
        for _ in range(total_degree):
            self.powers.append(meter.integer(self.powers[-1] * denominator))
            meter.inc('denominator_power_multiplications')

    def make(self, coefficients, degree):
        coefficients = tuple(coefficients)
        if len(coefficients) != self.J or not 0 <= degree <= self.total_degree:
            raise ValueError('invalid declared homogeneous degree')
        self.meter.max_declared_degree = max(self.meter.max_declared_degree, degree)
        return Jet(tuple(self.meter.integer(x) for x in coefficients), degree)

    def const(self, value, degree=0):
        return self.make((value * self.powers[degree],) + (0,) * (self.J - 1), degree)

    def add(self, left, right):
        if left.degree != right.degree:
            raise ValueError('addition requires equal denominator degrees')
        self.meter.inc('integer_additions', self.J)
        return self.make((a+b for a, b in zip(left.coefficients, right.coefficients)), left.degree)

    def negate(self, value):
        self.meter.inc('integer_negations', self.J)
        return self.make((-x for x in value.coefficients), value.degree)

    def mul(self, left, right):
        out = [0] * self.J
        for i, a in enumerate(left.coefficients):
            for j in range(self.J-i):
                v = self.meter.integer(a * right.coefficients[j])
                out[i+j] = self.meter.integer(out[i+j] + v)
                self.meter.inc('integer_multiplications')
                self.meter.inc('integer_additions')
        return self.make(out, left.degree + right.degree)

    def decode(self, value):
        return tuple(Fraction(x, self.powers[value.degree]) for x in value.coefficients)

    def tensor(self, truth, ports):
        if len(truth) != 1 << len(ports):
            raise ValueError('truth-table dimension mismatch')
        current = [self.const(int(v)) for v in truth]
        # Little-endian table indices: eliminate bit 0, then bit 1, etc.
        for port in ports:
            complement = self.add(self.const(1, 1), self.negate(port))
            current = [self.add(self.mul(complement, current[i]),
                                self.mul(port, current[i+1]))
                       for i in range(0, len(current), 2)]
        return current[0]


def bits(mask, width):
    return tuple((mask >> i) & 1 for i in range(width))


def count(n, factors, layout, *, validate=True):
    """Count from actual original predicates and an acquired source layout.

    The public factor() wrapper below acquires this layout itself. The generic
    interface has the same algebraic requirements as the pinned reference.
    Counters record operations, not a complete primitive-bit runtime.
    """
    ref = reference()
    factors = tuple(factors)
    if validate:
        ref.validate(n, factors, layout)
    M = sum(len(f.scope) for f in factors)
    J = M * layout.R // layout.Q + 1
    meter = Meter()
    truth = []
    for f in factors:
        table = []
        for mask in range(1 << len(f.scope)):
            raw = f.entry(bits(mask, len(f.scope)))
            if raw not in (0, 1):
                raise ValueError('Boolean entries required for the resource theorem')
            table.append(int(raw))
            meter.inc('original_predicate_calls')
        truth.append(tuple(table))
    # Materialize EVERY source coefficient once and acquire its common denominator.
    source = {}
    denominator = 1
    for e, f in enumerate(factors):
        for v in f.scope:
            row = {i: tuple(map(Fraction, a)) for i, a in layout.form(e, v).items()}
            source[e, v] = row
            for a in row.values():
                for c in a:
                    denominator = lcm(denominator, c.denominator)
                    meter.inc('source_lcm_steps')
    ops = HomogeneousJets(J, denominator, M, meter)
    scaled = {key: {i: tuple(int(c * denominator) for c in a) for i, a in row.items()}
              for key, row in source.items()}
    packets = {}
    for t in range(1, layout.Q+1):
        groups = tuple(tuple(g) for g in layout.groups(t))
        assigned = [[] for _ in groups]
        for e in range(len(factors)):
            assigned[layout.factor_group(t, e)].append(e)
        degrees = [sum(len(factors[e].scope) for e in es) for es in assigned]
        # Acquire head assignment lists, grouped by their ACTUAL measurement.
        buckets = []
        for g, group in enumerate(groups):
            rows = tuple(layout.measurement_rows(t, g))
            table = {}
            for mask in range(1 << len(group)):
                word = bits(mask, len(group))
                y = tuple(sum(a*b for a, b in zip(row, word)) for row in rows)
                table.setdefault(y, []).append(word)
                meter.inc('head_assignments_materialized')
            buckets.append(table)
        shifted = {}
        for key, row in scaled.items():
            shifted[key] = {}
            for i, coefficients in row.items():
                arr = [0]*J
                for d, c in enumerate(coefficients):
                    for k in range(min(d, J-1)+1):
                        arr[k] += c * comb(d, k) * t**(d-k)
                        meter.integer(arr[k])
                        meter.inc('source_shift_terms')
                shifted[key][i] = tuple(arr)
        H = ops.const(0, M)
        for size in range(min(J-1, n)+1):
            for S in combinations(range(n), size):
                for mask in range(1 << size):
                    U = {v for j, v in enumerate(S) if mask >> j & 1}
                    corrections = {key: (0,) + tuple(sum(a[k] for i, a in row.items() if i in U)
                                                      for k in range(1, J))
                                   for key, row in shifted.items()}
                    total = ops.const(0, M)
                    # At most the full summary-box size Y; never product of full head assignments.
                    for labels in product(*(tuple(b) for b in buckets)):
                        x = [0]*n
                        for g, group in enumerate(groups):
                            for i, bit in zip(group, buckets[g][labels[g]][0]):
                                x[i] = bit
                        accumulated = ops.const(1)
                        for g, group in enumerate(groups):
                            subtotal = ops.const(0, degrees[g])
                            for word in buckets[g][labels[g]]:
                                if any(i in S and not bit for i, bit in zip(group, word)):
                                    continue
                                for i, bit in zip(group, word):
                                    x[i] = bit
                                value = ops.const(1)
                                for e in assigned[g]:
                                    ports = []
                                    for v in factors[e].scope:
                                        key = e, v
                                        base = sum(a[0]*x[i] for i, a in shifted[key].items())
                                        ports.append(ops.make((base,) + corrections[key][1:], 1))
                                    value = ops.mul(value, ops.tensor(truth[e], ports))
                                    meter.inc('factor_interpolations')
                                subtotal = ops.add(subtotal, value)
                            accumulated = ops.mul(accumulated, subtotal)
                            for i, bit in zip(group, buckets[g][labels[g]][0]):
                                x[i] = bit
                        total = ops.add(total, accumulated)
                        meter.inc('attained_summary_visits')
                    H = ops.add(H, ops.negate(total) if (size-len(U)) % 2 else total)
                    meter.inc('support_pair_visits')
        packets[t] = ops.decode(H)
    # Polynomial-size exact Hermite recovery, reusing the pinned routine.
    recovery_stats = ref.Stats()
    result = ref.hermite_at_zero(packets, ref.Jets(J, recovery_stats))
    return dict(value=result, n=n, M=M, J=J, source_denominator=denominator,
                counts=meter.counts, maximum_recorded_integer_bits=meter.max_integer_bits,
                maximum_declared_degree=meter.max_declared_degree,
                recovery=recovery_stats.output(),
                resource_scope='operation diagnostics; theorem gives separate asymptotic bit bound')


def factor(N):
    """Original integer input: source acquisition, paid counter, and prefix recovery.

    No optional resource cap occurs in this mathematical algorithm. Invalid
    scheduled guards use the existing finite-prefix trial-division fallback.
    """
    if type(N) is not int or N < 2:
        raise ValueError('integer N>=2 required')
    load_file('source_parameters', SOURCE / 'source_parameters.py')
    load_file('source_layout', SOURCE / 'source_layout.py')
    search = load_file('_paid_source_search', SOURCE / 'source_factor_search.py')
    compiler, recovery = search.frozen_factor_modules()
    network = compiler.compile(N)
    search.check_input_coverage(network)
    scopes = tuple(tuple(v.ports) for v in network.vertices)
    st = search.scope_statistics(len(network.edges), scopes)
    p, guard = search.scheduled_guard(st['n'], st['M'], st['B'], st['w'])
    if not guard['accepted']:
        return dict(factors=recovery.direct_factor(N), method='finite_guard_fallback', count_queries=0)
    layout = search.construct_layout(st['n'], scopes, p, require_guard=True)
    queries = []
    ref = reference()
    def query(restricted):
        if tuple(tuple(v.ports) for v in restricted.vertices) != scopes:
            raise ValueError('prefix restriction changed original scopes')
        result = count(st['n'], tuple(ref.Factor(tuple(v.ports), v.entry) for v in restricted.vertices), layout)
        value = Fraction(result['value'])
        if value.denominator != 1 or value < 0:
            raise ArithmeticError('count recovery failed')
        queries.append(result)
        return value.numerator
    answer, used = recovery.recover_from_counter(network, query)
    return dict(factors=answer, method='paid_integer_source_counter', count_queries=used, queries=queries)
