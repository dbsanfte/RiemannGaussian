#!/usr/bin/env python3
"""Learn short kernel rules from anonymous impulse-response tables.

The learner never imports the benchmark's oracles or reads their labels. Its
assumptions are explicit: unary maps are modelled as linear and binary maps as
bilinear; a kernel is a small integer combination of index predicates, bounded
counts, or the inverse of a square predicate kernel. Dense validation happens in
the separate evaluator, so impulse responses alone cannot certify linearity.

Grammar: indices, constants 0..3, one + / - / * per index expression, equality
or <=, bounded sum over r=1..n, at most two kernel terms, matrix inversion.
There are no convolution, floor, divisibility, prime, gcd, or Mobius primitives.
All arithmetic is exact on this noise-free calibration dataset.
"""

from __future__ import annotations

import argparse
import itertools
import json
from fractions import Fraction
from pathlib import Path


def value(expr, indices):
    if expr[0] == "var":
        return indices[expr[1]]
    if expr[0] == "const":
        return expr[1]
    left, right = value(expr[1], indices), value(expr[2], indices)
    if expr[0] == "+":
        return left + right
    if expr[0] == "-":
        return left - right
    if expr[0] == "*":
        return left * right
    raise ValueError(expr[0])


def variables(expr):
    if expr[0] == "var":
        return {expr[1]}
    if expr[0] == "const":
        return set()
    return variables(expr[1]) | variables(expr[2])


def expression_cost(expr):
    return 1 if expr[0] in {"var", "const"} else 3


def expressions(names, multiply):
    leaves = [["var", name] for name in names]
    leaves += [["const", integer] for integer in range(4)]
    candidates = list(leaves)
    for operator in (["+", "-", "*"] if multiply else ["+", "-"]):
        for left, right in itertools.product(leaves, repeat=2):
            candidates.append([operator, left, right])
    return [expr for expr in candidates if variables(expr) == set(names)]


def atom_cost(program):
    return expression_cost(program["expr"]) + 1 + 2 * program["count"]


def cost(program):
    if program["kind"] == "atom":
        return atom_cost(program)
    if program["kind"] == "inverse":
        return 4 + cost(program["operand"])
    return 1 + sum(cost(term["program"]) + (term["coefficient"] != 1)
                   for term in program["terms"])


def atomic_programs(arity, multiply=True):
    families = [(False, ["i"] if arity == 1 else ["i", "j"])]
    if arity == 1:
        families.append((True, ["i", "r"]))
    programs = []
    for counted, names in families:
        for expr in expressions(names, multiply):
            for comparison in ("eq", "le"):
                programs.append({"kind": "atom", "expr": expr,
                                 "comparison": comparison, "count": counted})
    return sorted(programs, key=lambda item: (cost(item), json.dumps(item)))


def atom_kernel(program, arity, input_size, output_size):
    result = []
    for n in range(1, output_size + 1):
        for i in range(1, input_size + 1):
            for j in (range(1, input_size + 1) if arity == 2 else (None,)):
                indices = {"i": i, "j": j}
                total = 0
                for r in (range(1, n + 1) if program["count"] else (None,)):
                    indices["r"] = r
                    evaluated = value(program["expr"], indices)
                    total += int(evaluated == n if program["comparison"] == "eq"
                                 else evaluated <= n)
                result.append(total)
    return tuple(result)


def inverse_kernel(flat, size):
    """Gauss-Jordan inversion; works for any nonsingular rational matrix."""
    rows = [[Fraction(flat[n * size + i]) for i in range(size)]
            + [Fraction(n == i) for i in range(size)] for n in range(size)]
    for column in range(size):
        pivot = next((row for row in range(column, size)
                      if rows[row][column]), None)
        if pivot is None:
            raise ValueError("singular")
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [entry / scale for entry in rows[column]]
        for row in range(size):
            if row != column and rows[row][column]:
                factor = rows[row][column]
                rows[row] = [entry - factor * pivot_entry
                             for entry, pivot_entry in zip(rows[row], rows[column])]
    return tuple(entry for row in rows for entry in row[size:])


def kernel(program, arity, input_size, output_size):
    if program["kind"] == "atom":
        return atom_kernel(program, arity, input_size, output_size)
    if program["kind"] == "inverse":
        if arity != 1 or input_size != output_size:
            raise ValueError("Matrix inversion needs a square unary operator")
        return inverse_kernel(kernel(program["operand"], arity, input_size,
                                     output_size), input_size)
    pieces = [(term["coefficient"], kernel(term["program"], arity, input_size,
                                            output_size))
              for term in program["terms"]]
    return tuple(sum(coefficient * entries[index] for coefficient, entries in pieces)
                 for index in range(len(pieces[0][1])))


def scale_match(target, entries):
    first = next((index for index, entry in enumerate(entries) if entry), None)
    if first is None:
        return None
    coefficient = Fraction(target[first], entries[first])
    if coefficient.denominator != 1 or not 0 < abs(coefficient) <= 3:
        return None
    if all(expected == coefficient * actual for expected, actual in zip(target, entries)):
        return int(coefficient)
    return None


def pair_match(target, left, right):
    first = next((index for index, pair in enumerate(zip(left, right)) if any(pair)), None)
    if first is None:
        return None
    a, b, y = left[first], right[first], target[first]
    second = next((index for index, (c, d) in enumerate(zip(left, right))
                   if a * d - b * c), None)
    if second is None:
        return None
    c, d, z = left[second], right[second], target[second]
    determinant = a * d - b * c
    coefficients = (Fraction(y * d - b * z, determinant),
                    Fraction(a * z - y * c, determinant))
    if any(item.denominator != 1 or not 0 < abs(item) <= 3 for item in coefficients):
        return None
    u, v = coefficients
    if all(expected == u * x + v * w for expected, x, w in zip(target, left, right)):
        return int(u), int(v)
    return None


def scaled(program, coefficient):
    return program if coefficient == 1 else {
        "kind": "sum", "terms": [{"coefficient": coefficient, "program": program}]}


def make_dictionary(arity, input_size, output_size, multiply):
    unique = {}
    for program in atomic_programs(arity, multiply):
        entries = kernel(program, arity, input_size, output_size)
        if any(entries) and entries not in unique:
            unique[entries] = program
    return [(program, entries) for entries, program in unique.items()]


def recover(target, dictionary, arity, input_size, output_size, allow_inverse=True):
    matches, tested = [], 0
    for program, entries in dictionary:
        tested += 1
        coefficient = scale_match(target, entries)
        if coefficient is not None:
            matches.append(scaled(program, coefficient))
    # Two-term sparse models, with integer coefficients inferred from the data.
    for (left, left_entries), (right, right_entries) in itertools.combinations(dictionary, 2):
        tested += 1
        coefficients = pair_match(target, left_entries, right_entries)
        if coefficients is not None:
            matches.append({"kind": "sum", "terms": [
                {"coefficient": coefficients[0], "program": left},
                {"coefficient": coefficients[1], "program": right}]})
    if allow_inverse and arity == 1 and input_size == output_size:
        for program, entries in dictionary:
            tested += 1
            try:
                inverse = inverse_kernel(entries, input_size)
            except ValueError:
                continue
            coefficient = scale_match(target, inverse)
            if coefficient is not None:
                matches.append(scaled({"kind": "inverse", "operand": program}, coefficient))
    matches.sort(key=lambda item: (cost(item), json.dumps(item)))
    best = matches[0] if matches else None
    return {"program": best, "cost": cost(best) if best else None,
            "exact_training_match": best is not None, "matching_programs": len(matches),
            "candidate_models_checked": tested}


def render_expr(expr):
    if expr[0] in {"var", "const"}:
        return str(expr[1])
    return f"({render_expr(expr[1])} {expr[0]} {render_expr(expr[2])})"


def render(program, arity):
    if program is None:
        return "no rule in this grammar"
    if program["kind"] == "inverse":
        return "inverse(" + render(program["operand"], arity) + ")"
    if program["kind"] == "sum":
        return " + ".join(f"{term['coefficient']} * ({render(term['program'], arity)})"
                          for term in program["terms"])
    comparison = "=" if program["comparison"] == "eq" else "<="
    predicate = f"[{render_expr(program['expr'])} {comparison} n]"
    if program["count"]:
        predicate = f"sum(r=1..n, {predicate})"
    return f"sum(i, {predicate} * a[i])" if arity == 1 else (
        f"sum(i,j, {predicate} * a[i] * b[j])")


def apply_kernel(entries, inputs, output_size):
    features = inputs[0] if len(inputs) == 1 else [
        left * right for left in inputs[0] for right in inputs[1]]
    width = len(features)
    return [sum(coefficient * entry for coefficient, entry in
                zip(entries[n * width:(n + 1) * width], features))
            for n in range(output_size)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("training", type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--no-multiply", action="store_true")
    parser.add_argument("--no-inverse", action="store_true")
    args = parser.parse_args()
    dataset = json.loads(args.training.read_text())
    dictionaries, results = {}, {}
    for identifier, case in dataset["cases"].items():
        shape = (case["arity"], case["input_size"], case["output_size"])
        if shape not in dictionaries:
            dictionaries[shape] = make_dictionary(*shape, multiply=not args.no_multiply)
        result = recover(case["basis_responses"], dictionaries[shape], *shape,
                         allow_inverse=not args.no_inverse)
        result["rule"] = render(result["program"], case["arity"])
        results[identifier] = result
    output = {"grammar": {"index_operators": ["+", "-"] + ([] if args.no_multiply else ["*"]),
                          "comparisons": ["=", "<="], "auxiliary_bound": "1..n",
                          "max_index_expression_nodes": 3, "max_kernel_terms": 2,
                          "integer_coefficient_bound": 3,
                          "matrix_inverse": not args.no_inverse}, "cases": results}
    args.output.write_text(json.dumps(output, indent=2) + "\n")
    print(f"Learned a training rule for {sum(r['exact_training_match'] for r in results.values())}"
          f"/{len(results)} anonymous cases")


if __name__ == "__main__":
    main()
