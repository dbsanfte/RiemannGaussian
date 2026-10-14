#!/usr/bin/env python3
"""Enumerate raw integer and prime-power fibres before decoding their laws."""

from fractions import Fraction as Q
from pathlib import Path
import json
import time

from exact_arithmetic import factorization

BASE = Path(__file__).resolve().parent


def prime_powers(cutoff):
    out = []
    for n in range(2, cutoff + 1):
        f = factorization(n)
        if len(f) == 1:
            p, e = next(iter(f.items()))
            out.append((n, p, e))
    return out


def inspect(values, r=3):
    fibres = {}
    for j, a in enumerate(values):
        for b in values[j:]:
            n = a * b * (a + b) ** r
            fibres.setdefault(n, []).append((a, b))
    collisions = [(n, pairs) for n, pairs in fibres.items() if len(pairs) > 1]
    return {'input_count': len(values), 'unordered_pairs': len(values) * (len(values) + 1) // 2,
            'distinct_output_count': len(fibres), 'collision_count': len(collisions),
            'first_collisions': [{'output': n, 'pairs': pairs} for n, pairs in sorted(collisions)[:20]]}, fibres


def main():
    started = time.monotonic()
    integer, _ = inspect(list(range(2, 513)))
    pp = prime_powers(4096)
    prime_power, fibres = inspect([n for n, p, e in pp])
    prime, _ = inspect([n for n, p, e in pp if e == 1])
    deep_values = sorted(p ** e for p in range(2, 98) if factorization(p) == {p: 1} for e in range(1, 13))
    deep, _ = inspect(deep_values)
    # A reproducible high-index collision family is saved separately;
    # it is not mislabelled as a prime-power-input collision.
    family = []
    for t in (33, 37, 64, 101):
        a, b, c, d = 2 * (t - 32), 2 * t * (t - 1), 32 * (t - 1), t * (t - 32)
        left, right = a * b * (a + b) ** 3, c * d * (c + d) ** 3
        family.append({'t': t, 'left_pair': [a, b], 'right_pair': [c, d],
                       'output': left, 'equal': left == right,
                       'all_inputs_prime_powers': all(len(factorization(n)) == 1 for n in (a, b, c, d))})
    out = {'r': 3, 'integer_cutoff': 512, 'prime_power_cutoff': 4096,
           'integer_input_probe': integer, 'prime_power_input_probe': prime_power, 'prime_input_probe': prime,
           'deep_prime_power_probe': deep, 'deep_input_scope': 'Prime bases<=97, exponents 1..12; no output factorization assumed',
           'large_integer_collision_controls': family,
           'all_prime_power_fibres_injective_claimed': False,
           'seconds': time.monotonic() - started}
    dest = BASE / 'decode-results'
    dest.mkdir(exist_ok=True)
    (dest / 'pair_fibre_probe.json').write_text(json.dumps(out, indent=2) + '\n')
    for label in ('integer_input_probe', 'prime_power_input_probe', 'prime_input_probe', 'deep_prime_power_probe'):
        print(label, {k: v for k, v in out[label].items() if k != 'first_collisions'}, out[label]['first_collisions'][:2], flush=True)
    print('Large integer collision controls:', all(x['equal'] for x in family), 'seconds', out['seconds'], flush=True)


if __name__ == '__main__':
    main()
