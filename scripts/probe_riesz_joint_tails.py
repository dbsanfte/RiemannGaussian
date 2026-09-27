#!/usr/bin/env python3
"""Optional floating diagnostic of the literal binomial allocation tails.

Use the exact unpaid-order endpoints proved for N >= 320. No prime-density
model, zero hypothesis, or exhaustive certificate verification is used.
This is not directed-rounded arithmetic. The proofs of growth are in
ZetaRieszJointTailAudit.lean, not in this diagnostic.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path


U = 10001 / 20000
ORDERS = [320, 640, 1536, 8192, 65536, 262144, 1048576, 4194304]


def log_atom(n, k, x):
    return (math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)
            + k * math.log(x) + (n - k) * math.log1p(-x))


def log_tail(n, k, x, upper):
    """Sum a tail outwards from its largest atom, retaining its endpoint."""
    if not 0 <= k <= n:
        raise ValueError('Invalid tail endpoint')
    if (upper and k < n * x) or (not upper and k > n * x):
        raise ValueError('Recurrence must proceed away from the mean')
    total = term = 1.0
    j = k
    while (j < n if upper else j > 0):
        ratio = ((n - j) * x / ((j + 1) * (1 - x)) if upper else
                 j * (1 - x) / ((n - j + 1) * x))
        term *= ratio
        total += term
        j += 1 if upper else -1
        # Successive ratios decrease. This is a floating stopping rule,
        # not a rigorous enclosure of rounding or truncation error.
        if term / (1 - ratio) < 1e-16 * total:
            break
    return log_atom(n, k, x) + math.log(total)


def log_add(a, b):
    hi, lo = max(a, b), min(a, b)
    return hi + math.log1p(math.exp(lo - hi))


def exact_order_tail(order, x, assigned):
    # mem_unpaid_iff: k <= floor(13*N/32), 5*(N+1-k) < 4*N.
    if order < 320:
        raise ValueError('Endpoint theorem requires N >= 320')
    lo, hi = order // 5 + 2, 13 * order // 32
    n = order + 1
    low = log_tail(n, lo - 1, x, upper=False)
    if assigned:
        through_hi = log_tail(n, hi, x, upper=False)
        result = through_hi + math.log1p(-math.exp(low - through_hi))
    else:
        result = log_add(low, log_tail(n, hi + 1, x, upper=True))
    return result, lo, hi


def direct_check(order, x, assigned):
    """Independent small-order enumeration checks endpoints and recurrence."""
    n = order + 1
    logs = [log_atom(n, k, x) for k in range(n + 1)
            if ((k <= 13 * order // 32 and 5 * (order + 1 - k) < 4 * order)
                == assigned)]
    maximum = max(logs)
    direct = maximum + math.log(math.fsum(math.exp(a - maximum) for a in logs))
    recurrent, _, _ = exact_order_tail(order, x, assigned)
    discrepancy = abs(direct - recurrent)
    if discrepancy >= 1e-10:
        raise ArithmeticError('Tail recurrence disagrees with full enumeration')
    return discrepancy


def row(order):
    result = {'N': order, 'scaled_log_growth': (order + 1) * math.log1p(0.0001)}
    for name, x, assigned, base in [('assigned_at_59_percent', .41, True, 1001 / 1000),
                                    ('missing_at_60_percent', .4, False, 2001 / 2000)]:
        tail, lo, hi = exact_order_tail(order, x, assigned)
        result[name] = {
            'unpaid_orders': [lo, hi],
            'log_tail': tail,
            'log_source_scaled_tail': tail + result['scaled_log_growth'],
            'log_Lean_lower_bound': (order // 32) * math.log(base)
                                     - math.log(3 * (order + 1)),
        }
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    p = 13 / 32
    rates = []
    for x in [.41, .4]:
        entropy = p * math.log(p / x) + (1 - p) * math.log((1 - p) / (1 - x))
        rates.append({'cofactor_share': x, 'binomial_entropy': entropy,
                      'net_log_rate': math.log1p(.0001) - entropy})
    report = {
        'scope': 'Uncertified scalar-tail diagnostic; no bound for the signed prime sum',
        'radius_ceiling': U,
        'source_scaling': '(2*U)^(N+1)',
        'unpaid_order_definition': 'k <= floor(13*N/32) and 5*(N+1-k) < 4*N',
        'N_requirement': 'N >= 320; displayed Lean lower bounds also use 32 dividing N',
        'asymptotic_float_rates': rates,
        'enumeration_discrepancies': [direct_check(n, x, assigned)
                                     for n in [320, 640, 1536]
                                     for x, assigned in [(.41, True), (.4, False)]],
        'rows': [row(n) for n in ORDERS],
        'limitations': [
            'Floating lgamma and positive recurrences; no certified numerical intervals',
            'Both literal unpaid-order endpoints are retained',
            'A scalar tail is not the boundedShare of an actual integer label',
            'No prime-population, radial integral, phase, or signed-core bound is inferred',
            'Does not obstruct signed cancellation or the already paid outer radial regions',
        ],
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    for r in report['rows']:
        print(r['N'], r['assigned_at_59_percent']['log_source_scaled_tail'],
              r['missing_at_60_percent']['log_source_scaled_tail'])


if __name__ == '__main__':
    main()
