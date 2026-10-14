"""Frozen structural enumeration and selection for reversible arithmetic circuits."""
from copy import deepcopy
from fractions import Fraction as Q
import json
import random

import reversible_divisor_circuits as L

TRAIN = [32, 64, 128, 256]
VALIDATION = [384, 512, 768, 1024]
FINAL = [6144, 8192, 12288, 16384]
LEVELS = [2, 3, 6, 12]
FAMILIES = ['single_convolution', 'modulated_input', 'interleaved', 'double_interleaved']
FLAGS = dict(moment_estimate_proved=False, global_bound_proved=False, RH_proved=False)
ALPHAS = ['-1', '-1/2', '-1/3', '-1/6', '1/6', '1/3', '1/2', '1']
PRIME_PHASES = [
    ['constant', 1], ['constant', -1],
    ['parity', ['root', 1, 2]], ['parity', ['root', 1, 3]],
    ['residue_sign', ['n'], 3, [1]], ['residue_sign', ['n'], 5, [1, 4]],
    ['source_sign', ['root', 1, 2]], ['source_sign', ['subtract_root', 1, 2]]]
SIGNS = [
    ['source_sign', ['n']], ['source_sign', ['subtract_root', 1, 2]],
    ['source_sign', ['subtract_root', 1, 3]], ['source_sign', ['root', 1, 6]],
    ['parity', ['root', 2, 3]], ['parity', ['quotient', 2]],
    ['residue_sign', ['n'], 7, [1, 2, 4]],
    ['multiply', ['source_sign', ['n']], ['parity', ['root', 1, 3]]]]


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)


def generate(meter):
    """Parameters/circuit words are sampled before any arithmetic responses exist."""
    rng = random.Random(90317)
    records = []

    def add(family, program):
        meter.charge(len(canonical(program)) + len(records))
        if any(r['program'] == program for r in records):
            return False
        cert = L.certificate(program, meter)
        records.append(dict(id=len(records), family=family, program=program,
                            certificate=cert, inverse=L.inverse(program, meter),
                            complexity=len(canonical(program))))
        return True

    def convolution(alpha=None, phase=None):
        return dict(op='convolve', alpha=alpha or rng.choice(ALPHAS),
                    prime_phase=deepcopy(phase if phase is not None else rng.choice(PRIME_PHASES)))

    def sign(phase=None):
        return dict(op='sign', phase=deepcopy(phase if phase is not None else rng.choice(SIGNS)))

    add('baseline', {'stages': []})
    for family in FAMILIES:
        count = 0
        while count < 16:
            meter.charge()
            # The first factors cycle through every exponent and phase family;
            # extra factors are source-free draws from the complete declared lists.
            first = convolution(ALPHAS[count % len(ALPHAS)], PRIME_PHASES[(count // 2) % len(PRIME_PHASES)])
            if family == 'single_convolution':
                stages = [first]
            elif family == 'modulated_input':
                stages = [sign(SIGNS[count % len(SIGNS)]), first]
            elif family == 'interleaved':
                second = convolution()
                if count % 4 == 0:
                    # A generic conjugation production explores exact involutions
                    # as well as unrelated transform words, without response input.
                    second = deepcopy(first)
                    second['alpha'] = str(-Q(first['alpha']))
                stages = [first, sign(SIGNS[count % len(SIGNS)]), second]
            else:
                stages = [first, sign(SIGNS[count % len(SIGNS)]), convolution(), sign(), convolution()]
            if add(family, {'stages': stages}):
                count += 1
    meter.live(200000)
    return records


def ceil_root(X, q, meter):
    k = L.root(X, 1, q, meter)
    return k if meter.number(k ** q) == X else k + 1


def constants(cases, meter):
    result = {}
    for q in LEVELS:
        maximum = Q(0)
        for case in cases:
            meter.charge()
            maximum = max(maximum, meter.number(Q(case['energy']) / ceil_root(case['X'], q, meter)))
        result[str(q)] = str(maximum)
    return result


def scores(cases, fitted, meter):
    result = []
    for case in cases:
        for q in LEVELS:
            bound = meter.number(Q(fitted[str(q)]) * ceil_root(case['X'], q, meter))
            meter.charge()
            result.append(dict(X=case['X'], q=q, bound=str(bound),
                               passed=Q(case['energy']) <= bound,
                               dyadic=case['X'] & (case['X'] - 1) == 0))
    return result


def conditional_cost(record, row, q, meter):
    """A valid H_(1/2+1/q) bound IF the unproved cofinal moment law holds."""
    R = record['certificate']['recovery_power']
    result = (1 + q) ** (2 * R) * (Q(row['initial_cost']) + 4 * q * Q(row['constants'][str(q)]))
    return meter.number(result)


def choose(records, evidence, meter):
    by_id = {r['id']: r for r in records}
    ranked = []
    for row in evidence:
        meter.charge()
        if row['id'] == 0 or row['status'] != 'available':
            continue
        record = by_id[row['id']]
        key = (sum(not v['passed'] for v in row['scores']),
               tuple(conditional_cost(record, row, q, meter) for q in reversed(LEVELS)),
               record['complexity'], record['id'])
        ranked.append((key, record))
    ranked.sort(key=lambda item: item[0])
    chosen = []
    for family in FAMILIES:
        chosen.extend([r for _, r in ranked if r['family'] == family][:2])
    return chosen


def obligation(record):
    return dict(id=record['id'], program=record['program'], certificate=record['certificate'],
                target='complete actual Mobius prefix after the fixed circuit',
                required='For cofinally many integers q>0, exists finite C_q independent of every dyadic X>=32: D(X)<=C_q*ceil(X^(1/q))',
                source_binding='all actual primes/source coefficients, same source in every circuit stage and inverse',
                recovery='uniform finite-horizon discrete weighted L2; inverse cost included; fixed finite head retained',
                all_mixed_terms_retained=True, **FLAGS)
