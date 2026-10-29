"""Scratch exact colour/boundary contraction, independent of the Riemann tree.

The general proof and bit-cost model are in RESEARCH.txt.  This executable uses
Python tables to validate semantics, not to certify primitive machine clocks.
Only the testing code uses pseudorandom values; the algorithm is deterministic.
"""

from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
from math import prod


@dataclass(frozen=True)
class Graph:
    vertices: int
    edges: tuple[tuple[int, int], ...]

    def __post_init__(self):
        if self.vertices < 0:
            raise ValueError("negative vertex count")
        for u, v in self.edges:
            if not (0 <= u < self.vertices and 0 <= v < self.vertices):
                raise ValueError("endpoint outside the graph")
            if u == v:
                raise ValueError("the proved theorem assumes no loops")

    @property
    def ports(self):
        return tuple(tuple(e for e, ends in enumerate(self.edges) if v in ends)
                     for v in range(self.vertices))

    @property
    def degree(self):
        return max(map(len, self.ports), default=0)


class TruncatedRing:
    """Z/modulus with optional commuting truncated polynomial axes.

    axes=(2,) is a square-zero marker; axes=(2,3) retains a whole small jet.
    No inverse, field assumption, or coefficient-size oracle is used.
    """

    def __init__(self, modulus, axes=()):
        if modulus < 2 or any(q <= 0 for q in axes):
            raise ValueError("invalid modulus or axis")
        self.modulus, self.axes = modulus, tuple(axes)
        self.indices = tuple(product(*(range(q) for q in axes)))
        self.rank = prod(axes)
        self.zero = (0,) * self.rank
        self.one = (1,) + (0,) * (self.rank - 1)
        address = {a: i for i, a in enumerate(self.indices)}
        self.products = []
        for i, a in enumerate(self.indices):
            for j, b in enumerate(self.indices):
                c = tuple(x + y for x, y in zip(a, b))
                if all(x < q for x, q in zip(c, self.axes)):
                    self.products.append((i, j, address[c]))

    def valid(self, value):
        return len(value) == self.rank and all(0 <= x < self.modulus for x in value)

    def add(self, a, b):
        return tuple((x + y) % self.modulus for x, y in zip(a, b))

    def mul(self, a, b):
        out = [0] * self.rank
        for i, j, k in self.products:
            out[k] = (out[k] + a[i] * b[j]) % self.modulus
        return tuple(out)


def loads(k):
    return tuple(("bucket", g) for g in range(k)) + tuple(("merge", j) for j in range(2, k + 1))


def indicator(load, a, b):
    kind, p = load
    if kind == "bucket":
        return int(a == p or b == p)
    def region(c):
        return 0 if c < p - 1 else (1 if c == p - 1 else 2)
    return int(region(a) != region(b))


def mean_load(m, k, load):
    kind, p = load
    if kind == "bucket":
        return Q(m * (2 * k - 1), k * k)
    return Q(2 * m * (p * (k - p + 1) - 1), k * k)


@lru_cache(maxsize=100000)
def local_probability(k, load, endpoint_pairs, fixed):
    """Exact expectation of one or two indicators on at most four vertices."""
    unknown = tuple(i for i, value in enumerate(fixed) if value < 0)
    successes = 0
    colours = list(fixed)
    for values in product(range(k), repeat=len(unknown)):
        for i, value in zip(unknown, values):
            colours[i] = value
        successes += prod(indicator(load, colours[u], colours[v]) for u, v in endpoint_pairs)
    return Q(successes, k ** len(unknown))


def probability(graph, k, load, edge_ids, colours):
    vertices = tuple(sorted({v for e in edge_ids for v in graph.edges[e]}))
    address = {v: i for i, v in enumerate(vertices)}
    pairs = tuple((address[graph.edges[e][0]], address[graph.edges[e][1]]) for e in edge_ids)
    return local_probability(k, load, pairs, tuple(colours[v] for v in vertices))


def potential(graph, k, colours):
    """Conditional E sum_X (X - unconditional_mean(X))^2.

    Disjoint edges stay independent after fixing vertex colours.  This avoids
    enumerating their joint probabilities; parallel edges remain included.
    """
    m = len(graph.edges)
    shared = tuple((e, f) for e, f in combinations(range(m), 2)
                   if set(graph.edges[e]) & set(graph.edges[f]))
    out = Q(0)
    for load in loads(k):
        ps = [probability(graph, k, load, (e,), colours) for e in range(m)]
        variance = sum((p * (1 - p) for p in ps), Q(0))
        for e, f in shared:
            variance += 2 * (probability(graph, k, load, (e, f), colours) - ps[e] * ps[f])
        out += variance + (sum(ps, Q(0)) - mean_load(m, k, load)) ** 2
    return out


def choose_k(graph):
    m, degree = len(graph.edges), graph.degree
    if m == 0:
        return 2
    k = 2
    while k ** 3 * degree < m:
        k += 1
    return k


def load_values(graph, k, colours):
    return tuple(sum(indicator(load, colours[u], colours[v]) for u, v in graph.edges)
                 for load in loads(k))


def deterministic_colouring(graph, k=None):
    k = choose_k(graph) if k is None else k
    if k < 2:
        raise ValueError("at least two colours are required")
    colours = [-1] * graph.vertices
    current = potential(graph, k, colours)
    initial = current
    trace = [current]
    for v in range(graph.vertices):
        candidates = []
        for colour in range(k):
            colours[v] = colour
            candidates.append(potential(graph, k, colours))
        assert sum(candidates, Q(0)) / k == current, "conditional expectation identity failed"
        chosen = min(range(k), key=lambda colour: (candidates[colour], colour))
        colours[v], current = chosen, candidates[chosen]
        assert current <= trace[-1]
        trace.append(current)
    m = len(graph.edges)
    variance_bound = Q((2 * k - 1) * m * graph.degree, 2)
    assert initial <= variance_bound
    values = load_values(graph, k, colours)
    assert current == sum(((Q(value) - mean_load(m, k, load)) ** 2
                           for load, value in zip(loads(k), values)), Q(0))
    assert current <= initial
    for load, value in zip(loads(k), values):
        assert (Q(value) - mean_load(m, k, load)) ** 2 <= variance_bound
    stats = {"k": k, "colours": colours, "loads": list(values),
             "width": max(values, default=0),
             "initial_potential": str(initial), "final_potential": str(current),
             "variance_bound": str(variance_bound), "colour_steps": len(trace) - 1}
    return tuple(colours), stats


def validate_tables(graph, ring, tables):
    if len(tables) != graph.vertices:
        raise ValueError("one table is needed at every vertex, including isolated vertices")
    for ports, table in zip(graph.ports, tables):
        if len(table) != 1 << len(ports) or not all(ring.valid(x) for x in table):
            raise ValueError("malformed local table")


def project(bits, old_ports, new_ports):
    address = {e: i for i, e in enumerate(old_ports)}
    return sum(((bits >> address[e]) & 1) << i for i, e in enumerate(new_ports))


def brute_contract(graph, ring, tables):
    validate_tables(graph, ring, tables)
    answer = ring.zero
    all_ports = tuple(range(len(graph.edges)))
    for bits in range(1 << len(all_ports)):
        value = ring.one
        for ports, table in zip(graph.ports, tables):
            value = ring.mul(value, table[project(bits, all_ports, ports)])
        answer = ring.add(answer, value)
    return answer


def boundary_contract(graph, ring, tables, k=None, colours=None):
    validate_tables(graph, ring, tables)
    if colours is None:
        colours, stats = deterministic_colouring(graph, k)
        k = stats["k"]
    else:
        if k is None or len(colours) != graph.vertices or any(c < 0 or c >= k for c in colours):
            raise ValueError("invalid explicit colouring")
        values = load_values(graph, k, colours)
        stats = {"k": k, "colours": list(colours), "loads": list(values),
                 "width": max(values, default=0)}
    original_ports = graph.ports
    buckets, dimensions, visits = [], [], 0
    for colour in range(k):
        selected = tuple(v for v in range(graph.vertices) if colours[v] == colour)
        incident = tuple(e for e, (u, v) in enumerate(graph.edges)
                         if colours[u] == colour or colours[v] == colour)
        boundary = tuple(e for e, (u, v) in enumerate(graph.edges)
                         if (colours[u] == colour) != (colours[v] == colour))
        result = [ring.zero] * (1 << len(boundary))
        dimensions.append(len(incident))
        for bits in range(1 << len(incident)):
            value = ring.one
            for v in selected:
                value = ring.mul(value, tables[v][project(bits, incident, original_ports[v])])
            output = project(bits, incident, boundary)
            result[output] = ring.add(result[output], value)
            visits += 1
        buckets.append((boundary, result))
    old_boundary, result = buckets[0]
    for new_boundary, new_table in buckets[1:]:
        union = tuple(sorted(set(old_boundary) | set(new_boundary)))
        output_boundary = tuple(sorted(set(old_boundary) ^ set(new_boundary)))
        next_table = [ring.zero] * (1 << len(output_boundary))
        dimensions.append(len(union))
        for bits in range(1 << len(union)):
            value = ring.mul(result[project(bits, union, old_boundary)],
                             new_table[project(bits, union, new_boundary)])
            output = project(bits, union, output_boundary)
            next_table[output] = ring.add(next_table[output], value)
            visits += 1
        old_boundary, result = output_boundary, next_table
    assert old_boundary == () and len(result) == 1
    assert dimensions == stats["loads"], "cost loads do not match the executed contraction"
    stats.update({"assignment_visits": visits, "brute_assignments": 1 << len(graph.edges),
                  "m": len(graph.edges), "degree": graph.degree, "ring_rank": ring.rank,
                  "modulus": ring.modulus})
    return result[0], stats
