"""Exact finite checks supporting, but not replacing, the proof in RESEARCH.txt."""

import json
from fractions import Fraction as Q
from itertools import product
from random import Random
from time import monotonic
from pathlib import Path

from boundary_hybrid import (Graph, TruncatedRing, boundary_contract, brute_contract,
                             deterministic_colouring, load_values, loads, mean_load,
                             potential)


def random_tables(graph, ring, seed):
    rng = Random(seed)
    return tuple(tuple(tuple(rng.randrange(ring.modulus) for _ in range(ring.rank))
                       for _ in range(1 << len(ports))) for ports in graph.ports)


def check_potential_exhaustively():
    # Parallel edges, an isolated vertex, and adjacent/disjoint pairs.
    graph = Graph(5, ((0, 1), (0, 1), (1, 2), (2, 3)))
    checks = 0
    for k in (2, 3):
        all_values = [[] for _ in loads(k)]
        for colours in product(range(k), repeat=graph.vertices):
            for dest, value in zip(all_values, load_values(graph, k, colours)):
                dest.append(value)
        for load, values in zip(loads(k), all_values):
            assert Q(sum(values), len(values)) == mean_load(len(graph.edges), k, load)
            checks += 1
        for fixed in ((-1, -1, -1, -1, -1), (0, -1, -1, -1, -1),
                      (0, 1, -1, -1, -1), (0, 0, 1, -1, -1)):
            samples = []
            unknown = [i for i, c in enumerate(fixed) if c < 0]
            for continuation in product(range(k), repeat=len(unknown)):
                colours = list(fixed)
                for i, c in zip(unknown, continuation):
                    colours[i] = c
                xs = load_values(graph, k, colours)
                samples.append(sum(((Q(x) - mean_load(len(graph.edges), k, load)) ** 2
                                    for load, x in zip(loads(k), xs)), Q(0)))
            assert sum(samples, Q(0)) / len(samples) == potential(graph, k, fixed)
            checks += 1
    return checks


def main():
    start = monotonic()
    potential_checks = check_potential_exhaustively()
    graphs = {
        "empty": Graph(0, ()),
        "isolated_only": Graph(3, ()),
        "parallel_and_isolated": Graph(4, ((0, 1), (0, 1), (0, 1))),
        "disconnected": Graph(7, ((0, 1), (1, 2), (0, 2), (3, 4), (3, 4))),
        "cycle12": Graph(12, tuple((i, (i + 1) % 12) for i in range(12))),
        "complete4": Graph(4, tuple((i, j) for i in range(4) for j in range(i + 1, 4))),
        "bipartite3x4": Graph(7, tuple((i, j) for i in range(3) for j in range(3, 7))),
        "star10": Graph(11, tuple((0, i) for i in range(1, 11))),
    }
    rings = (TruncatedRing(8), TruncatedRing(16, (2,)), TruncatedRing(8, (2, 3)))
    records = []
    for gi, (name, graph) in enumerate(graphs.items()):
        for k in (2, 4):
            colours, colour_stats = deterministic_colouring(graph, k)
            for ri, ring in enumerate(rings):
                tables = random_tables(graph, ring, seed=100 * gi + ri)
                actual, stats = boundary_contract(graph, ring, tables, k=k, colours=colours)
                expected = brute_contract(graph, ring, tables)
                assert actual == expected, (name, k, ring.axes, actual, expected)
                records.append({"graph": name, "axes": ring.axes, "value": actual,
                                **colour_stats, **stats})

    # Exhaustively test the contraction identity for every colouring of a small
    # parallel-edge graph, rather than only the greedy algorithm's selected one.
    small = Graph(3, ((0, 1), (0, 1), (1, 2)))
    ring = TruncatedRing(8, (2,))
    tables = random_tables(small, ring, 991)
    expected = brute_contract(small, ring, tables)
    arbitrary_colourings = 0
    for k in (2, 3):
        for colours in product(range(k), repeat=small.vertices):
            assert boundary_contract(small, ring, tables, k=k, colours=colours)[0] == expected
            arbitrary_colourings += 1

    # Retain an isolated zero and a non-unit factor (2 mod 8), never normalize it.
    graph = Graph(3, ((0, 1),))
    ring = TruncatedRing(8)
    for scalar, expected in ((0, 0), (2, 4)):
        tables = (((1,), (1,)), ((1,), (1,)), ((scalar,),))
        assert boundary_contract(graph, ring, tables)[0] == (expected,)

    # A square-zero marker carries an exact count plus its sum of marks.
    # Three equality-constrained wires give only all-zero and all-one assignments.
    graph = Graph(3, ((0, 1), (1, 2), (2, 0)))
    ring = TruncatedRing(64, (2,))
    marks = (3, 5, 7)
    tables = tuple(((1, 0), (0, 0), (0, 0), (1, mark)) for mark in marks)
    packed, packed_stats = boundary_contract(graph, ring, tables)
    assert packed == (2, sum(marks))

    # Dense jet multiplication must retain cross terms; top-level moment-only
    # cancellation is not used to drop intermediate jet coordinates.
    ring = TruncatedRing(8, (2, 3))
    x, y = (1, 2, 3, 4, 5, 6), (2, 1, 4, 3, 6, 5)
    graph = Graph(2, ((0, 1),))
    tables = ((x, ring.zero), (y, ring.zero))
    assert boundary_contract(graph, ring, tables)[0] == ring.mul(x, y)

    # Invalid incidence structures are rejected rather than using a theorem
    # that assumes every variable has two distinct incident vertices.
    rejected = 0
    for vertices, edges in ((1, ((0, 0),)), (2, ((0, 2),))):
        try:
            Graph(vertices, edges)
        except ValueError:
            rejected += 1
    assert rejected == 2

    # Exercise automatically selected K>2, and check that no floating cube-root
    # rounding affects the choice.  This is a colour check, not a 2^36 brute run.
    graph = Graph(36, tuple((i, (i + 1) % 36) for i in range(36)))
    _, larger_colour_stats = deterministic_colouring(graph)
    assert larger_colour_stats["k"] == 3

    result = {
        "status": "passed", "exact_semantic_comparisons": len(records),
        "exhaustive_conditional_expectation_checks": potential_checks,
        "arbitrary_colourings_checked": arbitrary_colourings,
        "isolated_scalar_checks": 2, "packed_count_first_moment": packed,
        "intermediate_jet_cross_terms": "passed", "invalid_graphs_rejected": rejected,
        "auto_colour_cycle36": larger_colour_stats,
        "elapsed_seconds": round(monotonic() - start, 4), "cases": records,
        "scope": "finite prototype validation; general exponent is proved in RESEARCH.txt"
    }
    destination = Path(__file__).with_name("validation.json")
    destination.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "cases"}, indent=2))


if __name__ == "__main__":
    main()
