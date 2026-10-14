#!/usr/bin/env python3
"""Search signed root-lift combinations and learn their projection identities.

Four orientations are ordered FF, FC, CF, CC. A linear combination of
root lifts is typed as an arithmetic operation, not automatically as an
associative product. Finite fits and universal certificates are distinct.
"""

from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial, gcd
from pathlib import Path
import json
import random
import time

from exact_arithmetic import convolve, factorization, sequence, unit
from joint_size_search import height, joint_product, weight


BASE = Path(__file__).resolve().parent
ORIENTATIONS = tuple(product(('floor', 'ceil'), repeat=2))
ATOM_NAMES = ('P', 'a*R_b(d)+R_b(a)*d', 'a*R_c(d)+R_c(a)*d', 'R_b(P)', 'R_c(P)',
              'a*R_bc(d)+R_bc(a)*d', 'R_b(a)*R_c(d)+R_c(a)*R_b(d)',
              'R_c(a*R_b(d)+R_b(a)*d)', 'R_b(a*R_c(d)+R_c(a)*d)', 'R_bc(P)')


def polynomial(q, mode, ceiling=False):
    if mode == 0:
        return {0: Q(1, factorial(q))}
    return {r: -Q((-1 if ceiling else 1) ** r, mode ** r * factorial(q - r))
            for r in range(1, q)}


def mul_poly(a, d):
    result = {}
    for i, x in a.items():
        for j, y in d.items():
            result[i + j] = result.get(i + j, Q(0)) + x * y
    return {k: v for k, v in result.items() if v}


def spectrum(q, m, n, weights):
    result = {}
    for coefficient, (o1, o2) in zip(weights, ORIENTATIONS):
        term = mul_poly(polynomial(q, m, o1 == 'ceil'), polynomial(q, n, o2 == 'ceil'))
        for degree, value in term.items():
            result[degree] = result.get(degree, Q(0)) + coefficient * value
    return {k: v for k, v in result.items() if v}


def primitive_weights():
    for values in product(range(-2, 3), repeat=4):
        first = next((x for x in values if x), None)
        if first is None or first < 0:
            continue
        divisor = 0
        for x in values:
            divisor = gcd(divisor, abs(x))
        if divisor == 1:
            yield values


def frequency_grammar():
    records = []
    fresh = ((1, 0), (0, 1), (2, -3), (-5, 7), (11, 13), (-17, -19))
    for q, coefficients in product(range(2, 9), tuple(primitive_weights())):
        training = not spectrum(q, 1, 1, coefficients)
        failure = next(([m, n] for m, n in fresh if spectrum(q, m, n, coefficients)), None) if training else [1, 1]
        u = sum(coefficients)
        v = sum(x * y for x, y in zip(coefficients, (1, -1, -1, 1)))
        x = sum(x * y for x, y in zip(coefficients, (1, 1, -1, -1)))
        y = sum(x * y for x, y in zip(coefficients, (1, -1, 1, -1)))
        classification = ('dense_mixed_artifacts' if q >= 3 or v else
                          'discrete_axis_artifacts' if x or y else 'all_artificial_Abelian_modes_cancel')
        records.append({'q': q, 'weights': list(coefficients), 'training_passed': training,
                        'held_out_passed': training and failure is None, 'first_failed_mode': failure,
                        'Hadamard_coordinates': [u, v, x, y], 'universal_domain_classification': classification})
    return {'models_scored': len(records), 'weights_per_root_order': len(tuple(primitive_weights())),
            'training_mode': [1, 1], 'fresh_modes': [list(x) for x in fresh],
            'training_fits': sum(x['training_passed'] for x in records),
            'survivors': [x for x in records if x['held_out_passed']], 'records': records,
            'universal_q2_survivor': 'All four weights equal; canonical primitive representative [1,1,1,1]',
            'universal_q_ge_3_result': 'Every nonzero rational constant orientation combination retains a dense artificial singularity set for independent bases',
            'finite_polynomial_checks_are_support_not_proof': True}


@lru_cache(maxsize=None)
def power_index(n, base):
    return n == base ** height(n, base)


def projection(a, base):
    return [value if n and power_index(n, base) else Q(0) for n, value in enumerate(a)]


def common_projection(a, b, c):
    return projection(projection(a, b), c)


def add(a, d):
    return [x + y for x, y in zip(a, d)]


def atoms(a, d, b, c):
    p = convolve(a, d)
    ab, db, ac, dc = projection(a, b), projection(d, b), projection(a, c), projection(d, c)
    bc_a, bc_d = common_projection(a, b, c), common_projection(d, b, c)
    one = add(convolve(a, db), convolve(ab, d))
    two = add(convolve(a, dc), convolve(ac, d))
    return [p, one, two, projection(p, b), projection(p, c),
            add(convolve(a, bc_d), convolve(bc_a, d)),
            add(convolve(ab, dc), convolve(ac, db)), projection(one, c), projection(two, b),
            common_projection(p, b, c)]


def orientation_sum(a, d, b, c):
    result = [Q(0)] * len(a)
    for o1, o2 in ORIENTATIONS:
        result = add(result, joint_product(a, d, b, c, o1, o2))
    return result


def fit_linear(rows, observations, columns):
    pivots = {}
    for values, target in zip(rows, observations):
        row = [Q(x) for x in values] + [Q(target)]
        for index in sorted(pivots):
            if row[index]:
                factor = row[index]
                row = [x - factor * y for x, y in zip(row, pivots[index])]
        index = next((k for k in range(columns) if row[k]), None)
        if index is None:
            if row[-1]:
                raise AssertionError('Grammar has no exact linear fit')
            continue
        divisor = row[index]
        row = [x / divisor for x in row]
        for other in tuple(pivots):
            if pivots[other][index]:
                factor = pivots[other][index]
                pivots[other] = [x - factor * y for x, y in zip(pivots[other], row)]
        pivots[index] = row
    assert len(pivots) == columns, 'Identity coefficients are not uniquely determined'
    return [pivots[k][-1] for k in range(columns)]


def identity_search():
    rng = random.Random(2026100704)
    training, fresh = [], []
    rows, targets = [], []
    for held_out, pairs, cutoff in ((False, ((2, 3), (2, 6), (4, 6), (2, 4)), 48),
                                  (True, ((4, 8), (3, 12), (6, 12), (5, 7)), 128)):
        for b, c in pairs:
            for _ in range(3):
                a, d = [sequence([Q(rng.randint(1, 4), rng.randint(1, 5))]
                                  + [Q(rng.randint(-3, 3), rng.randint(1, 7)) for _ in range(cutoff - 1)]) for j in range(2)]
                features = atoms(a, d, b, c)
                observed = orientation_sum(a, d, b, c)
                record = {'bases': [b, c], 'cutoff': cutoff, 'input_a': [str(x) for x in a],
                          'input_d': [str(x) for x in d], 'orientation_sum': [str(x) for x in observed]}
                if held_out:
                    fresh.append(record)
                else:
                    training.append(record)
                    rows += list(zip(*(x[1:] for x in features)))
                    targets += observed[1:]
    fitted = fit_linear(rows, targets, len(ATOM_NAMES))
    for item in fresh:
        a, d = [[Q(x) for x in item[key]] for key in ('input_a', 'input_d')]
        features = atoms(a, d, *item['bases'])
        predicted = [sum((coefficient * feature[n] for coefficient, feature in zip(fitted, features)), Q(0)) for n in range(len(a))]
        item['held_out_passed'] = [str(x) for x in predicted] == item['orientation_sum']
    return {'grammar_atoms': list(ATOM_NAMES), 'unique_fitted_coefficients': [str(x) for x in fitted],
            'exact_training_equations': len(rows), 'training_records': training, 'fresh_records': fresh,
            'all_held_out_passed': all(x['held_out_passed'] for x in fresh),
            'universal_identity_proof': 'Expand (1+I_b(a)+I_b(d)-I_b(ad))*(1+I_c(a)+I_c(d)-I_c(ad))'}


def associativity_controls():
    controls = []
    for b, c in ((2, 3), (2, 5), (4, 8), (2, 6)):
        def k(a, d):
            return Q(sum(weight(a, d, b, c, *o) for o in ORIENTATIONS), 4)
        witness = None
        for a, d, e in product(range(1, 25), repeat=3):
            left, right = k(a, d) * k(a * d, e), k(d, e) * k(a, d * e)
            if left != right:
                witness = {'a': a, 'd': d, 'e': e, 'left': str(left), 'right': str(right)}
                break
        controls.append({'bases': [b, c], 'normalized_average_kernel_counterexample': witness,
                         'scope': 'Both prime bases: classical nonzero weighted transport; composite cases require an independent algebra gate'})
    return controls


def root_sequence(beta, cutoff):
    out = [Q(0), Q(1)]
    for n in range(2, cutoff + 1):
        coefficient = Q(1)
        for e in factorization(n).values():
            for j in range(e):
                coefficient *= Q(beta + j, j + 1)
        out.append(coefficient)
    return out


def averaging_order_control():
    b, c, q, cutoff = 2, 3, 3, 16
    g = root_sequence(Q(1, q), cutoff)
    raw = [Q(0)] * len(g)
    for orientation in ORIENTATIONS:
        lifted = unit(cutoff)
        for _ in range(q):
            lifted = joint_product(lifted, g, b, c, *orientation)
        raw = add(raw, lifted)
    raw = [x / 4 for x in raw]
    averaged = unit(cutoff)
    for _ in range(q):
        averaged = [x / 4 for x in orientation_sum(averaged, g, b, c)]
    index = next(n for n in range(1, cutoff + 1) if raw[n] != averaged[n])
    return {'bases': [b, c], 'q': q, 'index': index, 'mean_of_four_lift_coefficients': str(raw[index]),
            'lift_of_mean_kernel_coefficient': str(averaged[index]), 'difference': str(averaged[index] - raw[index]),
            'averaging_and_taking_q_fold_lifts_are_not_interchangeable': raw[index] != averaged[index]}


def zeta_profiles(fitted, cutoff=4096):
    records = []
    for (b, c), beta in product(((2, 3), (2, 6), (4, 8)), (Q(1, 2), Q(1, 4))):
        g = root_sequence(beta, cutoff)
        features = atoms(g, g, b, c)
        observed = orientation_sum(g, g, b, c)
        prediction = [sum((x * v[n] for x, v in zip(fitted, features)), Q(0)) for n in range(cutoff + 1)]
        # Isolate the three g*projection terms, preserving an explicit
        # arithmetic expression on the original four joint products.
        corrected = [(observed[n] - features[0][n] + features[3][n] + features[4][n]
                      - features[6][n] + features[7][n] + features[8][n] - features[9][n]) / 6
                     for n in range(cutoff + 1)]
        projected = add(add(projection(g, b), projection(g, c)), common_projection(g, b, c))
        direct = [x / 3 for x in convolve(g, projected)]
        passed = observed == prediction and corrected == direct and all(0 <= x <= 1 for x in corrected)
        records.append({'bases': [b, c], 'beta': str(beta), 'cutoff': cutoff,
                        'sum_coefficients': [str(x) for x in observed],
                        'corrected_root_coefficients': [str(x) for x in corrected],
                        'learned_identity_and_direct_projection_agree': passed})
        print(f'Cancellation coefficients b,c={b},{c}, beta={beta}: {passed}', flush=True)
    return records


def main():
    started = time.monotonic()
    out = BASE / 'cancellation-results'
    out.mkdir(exist_ok=True)
    frequency = frequency_grammar()
    identity = identity_search()
    controls = associativity_controls()
    averaging = averaging_order_control()
    profiles = zeta_profiles([Q(x) for x in identity['unique_fitted_coefficients']])
    result = {'frequency_grammar': frequency, 'bilinear_projection_identity': identity,
              'associativity_controls': controls, 'actual_zeta_coefficient_profiles': profiles,
              'averaging_order_counterexample': averaging,
              'corrected_root_definition': '(sum_four_joint_squares-P+R_b(P)+R_c(P)-cross+R_c(first)+R_b(second)-R_bc(P))/6',
              'corrected_root_reduction': 'g*(R_b(g)+R_c(g)+R_bc(g))/3',
              'analytic_target': 'zeta^beta*(R_(b,beta)+R_(c,beta)+R_(bc,beta))/3, with R_bc=unit-only if no common positive powers',
              'universal_correction_nonzero_domain': 'Re(s)>0 for every beta in [0,1], by the established positive Hausdorff-moment theorem',
              'counts_as_new_primitive': False, 'new_RH_estimate_proved': False,
              'historical_originality': 'Unresolved; normalized survivor reduces to a sum of known paired-root compositions',
              'proof': 'cancellation_proof.txt',
              'all_passed': frequency['survivors'] == [x for x in frequency['records'] if x['q'] == 2 and x['weights'] == [1, 1, 1, 1]]
                            and identity['all_held_out_passed'] and all(x['learned_identity_and_direct_projection_agree'] for x in profiles)
                            and averaging['averaging_and_taking_q_fold_lifts_are_not_interchangeable'],
              'elapsed_seconds': time.monotonic() - started}
    (out / 'cancellation_search.json').write_text(json.dumps(result, indent=2) + '\n')
    print(f'Cancellation grammar: {frequency["models_scored"]} models, {frequency["training_fits"]} fits, '
          f'{len(frequency["survivors"])} survivor; all={result["all_passed"]}; elapsed={result["elapsed_seconds"]:.2f}s')
    assert result['all_passed']


if __name__ == '__main__':
    main()
