"""Independent checker scaffold for inverse-prefix response experiments.

Only check_inverse_prefix_math supplies arithmetic. Producer modules are never
imported. Functions return regenerated records and raise on mathematical errors;
the run-file schema is bound after joint review, before freezing.
"""

from fractions import Fraction as Q
from itertools import combinations, product
import hashlib
import json
from pathlib import Path
import argparse
import subprocess
import sys
import tempfile

from check_inverse_prefix_math import (
    convolution, inverse, prefix, prime_mu, safe_cutoff,
    signed_block_energies, solve_unique, truncated_components,
)


RECURRENCE_FEATURES = [
    'one', 'k', 'r', 'r_is_one', 'same', 'left', 'right',
    'previous', 'previous_left', 'k_same', 'r_same',
]


def json_exact(value):
    if isinstance(value, Q):
        return int(value) if value.denominator == 1 else str(value)
    if isinstance(value, dict):
        return {k: json_exact(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_exact(v) for v in value]
    return value


def digest(value):
    data = json.dumps(json_exact(value), sort_keys=True, separators=(',', ':'))
    return hashlib.sha256(data.encode()).hexdigest()


def file_sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def reference(seed, N):
    """Independent deterministic LCG replay of the declared input protocol."""
    if type(seed) is not int or type(N) is not int or N < 1:
        raise ValueError('integer seed and positive cutoff required')
    values = [0, 1]
    current = seed
    for _ in range(2, N + 1):
        current = (current * 1664525 + 1013904223) & 0xffffffff
        values.append(((current >> 11) % 5) - 2)
    return values


def integer_root(n, k):
    if type(n) is not int or n < 0 or type(k) is not int or k < 1:
        raise ValueError('nonnegative integer and positive arity required')
    if n < 2:
        return n
    if k >= n.bit_length():
        # 1**k<=n<2**k establishes the floor root without powering.
        return 1
    lo, hi = 0, n + 1
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if mid ** k <= n:
            lo = mid
        else:
            hi = mid
    return lo


def difference_coefficients(table):
    return [Q(0)] + [Q(table[n]) - Q(table[n - 1])
                     for n in range(1, len(table))]


def component_tables(h, a, u, k, N):
    good = truncated_components(h, a, u, k, N)
    # Wrong columns carry one extra h. Reconstruct the coefficient sequence
    # from each good prefix instead of reproducing the producer's power loop.
    wrong = [prefix(convolution(difference_coefficients(t), h, N))
             for t in good]
    return good, wrong


def feature_table(seed, N, arities, indices):
    h = reference(seed, N)
    a = inverse(h)
    target = prefix(a)
    rows = []
    for k in arities:
        for x in indices:
            if x < 1 or x > N:
                raise ValueError('response index lies outside reference prefix')
            root = integer_root(x, k)
            for offset in (0, 1):
                u = min(x, root + offset)
                good, wrong = component_tables(h, a, u, k, x)
                rows.append({
                    'arity': k, 'x': x, 'u': u,
                    'columns': json_exact([t[x] for t in good + wrong]
                                          + [1, sum(h[1:x + 1])]),
                    'anonymous_target': json_exact(target[x]),
                    'reference_id': digest(h),
                })
    return {'seed': seed, 'cutoff': N, 'reference': h,
            'inverse_sha256': digest(a), 'rows': rows,
            'prime_or_factor_oracle_used': False,
            'target_coefficients_supplied': False}


def recurrence_features(table, k, r, dictionary=RECURRENCE_FEATURES):
    def entry(j, s):
        row = table.get(str(j))
        return Q(row[s - 1]) if row is not None and 1 <= s <= len(row) else Q(0)
    same = entry(k, r)
    values = {
        'one': Q(1), 'k': Q(k), 'r': Q(r), 'r_is_one': Q(r == 1),
        'same': same, 'left': entry(k, r - 1), 'right': entry(k, r + 1),
        'previous': entry(k - 1, r), 'previous_left': entry(k - 1, r - 1),
        'k_same': k * same, 'r_same': r * same,
    }
    return [values[name] for name in dictionary]


def _unique_or_none(matrix, target):
    if not matrix:
        return None
    try:
        return solve_unique(matrix, target)
    except ValueError:
        return None


def infer(rows, arities, support_budget=3, dictionary=RECURRENCE_FEATURES):
    """Exhaustive exact sparse inference, with no expected weight vector."""
    learned, rejected, retained, attempts = {}, [], {}, {}
    for k in arities:
        samples = [row for row in rows if row['arity'] == k]
        if not samples:
            raise ValueError('missing arity response rows')
        width = len(samples[0]['columns'])
        if any(len(row['columns']) != width for row in samples):
            raise ValueError('inconsistent response dictionary width')
        fits, count = [], 0
        for size in range(1, k + 1):
            for support in combinations(range(width), size):
                count += 1
                solution = _unique_or_none(
                    [[row['columns'][j] for j in support] for row in samples],
                    [row['anonymous_target'] for row in samples])
                if solution is None or any(value == 0 for value in solution):
                    continue
                vector = [Q(0)] * width
                for j, value in zip(support, solution):
                    vector[j] = value
                fits.append({'support': list(support),
                             'weights': [str(value) for value in vector],
                             'expected_coefficients_supplied': False})
            if fits:
                break
        fits.sort(key=lambda fit: (len(str(fit['weights'])), digest(fit)))
        retained[str(k)], attempts[str(k)] = fits, count
        if fits:
            learned[str(k)] = fits[0]['weights']
        else:
            rejected.append({'arity': k,
                             'reason': 'inconsistent_or_nonunique_exact_response_fit'})
    table = {key: vector[:int(key)] for key, vector in learned.items()}
    examples = []
    for k in arities:
        if str(k + 1) not in table:
            continue
        for r in range(1, k + 3):
            y = Q(table[str(k + 1)][r - 1]) if r <= k + 1 else Q(0)
            examples.append((recurrence_features(table, k, r, dictionary), y))
    relations = []
    for size in range(1, support_budget + 1):
        for support in combinations(range(len(dictionary)), size):
            weights = _unique_or_none(
                [[x[j] for j in support] for x, _ in examples],
                [y for _, y in examples])
            if weights is None or any(value == 0 for value in weights):
                continue
            relations.append({
                'terms': [[dictionary[j], str(value)]
                          for j, value in zip(support, weights)],
                'support_size': size, 'exact_response_fit': True,
                'expected_recurrence_supplied': False,
            })
    relations.sort(key=lambda fit: (fit['support_size'], len(str(fit['terms'])), digest(fit)))
    return {'learned_vectors': learned, 'coefficient_table': table,
            'rejected_arity_fits': rejected,
            'retained_minimum_support_arity_fits': retained,
            'arity_supports_checked': attempts,
            'retained_recurrence_fits': relations,
            'selected_recurrence': relations[0] if relations else None,
            'initial_arity': min(arities),
            'initial_weights': table.get(str(min(arities))),
            'global_reconstruction_proved': False}


def continued_weights(model, k, promotion=True, dictionary=RECURRENCE_FEATURES):
    table = {key: list(row) for key, row in model['coefficient_table'].items()}
    if str(k) in table:
        return [Q(value) for value in table[str(k)]]
    relation = model['selected_recurrence']
    if not promotion or not table or relation is None:
        return None
    start = max(int(key) for key in table)
    if k < start:
        return None
    for j in range(start, k):
        row = []
        for r in range(1, j + 2):
            features = dict(zip(dictionary, recurrence_features(table, j, r, dictionary)))
            row.append(str(sum((Q(value) * features[name]
                                for name, value in relation['terms']), Q(0))))
        table[str(j + 1)] = row
    return [Q(value) for value in table[str(k)]]


def block_energy(sums, X):
    energy = signed_block_energies(sums, X)
    return {'energy': energy['A_X'], 'child_energy': energy['A_2X'],
            'signed_defect': energy['Delta']}


def actual_profile(scales, arities, model, promotion=True):
    """Independent factor-sieve actual arithmetic and exact signed moments."""
    N = 4 * max(scales)
    mu = prime_mu(N)
    sums = prefix(mu)
    h = [0] + [1] * N
    rows = []
    for X in scales:
        for k in arities:
            weights = continued_weights(model, k, promotion)
            if weights is None:
                rows.append({'X': X, 'arity': k, 'missing': True})
                continue
            u = safe_cutoff(X, k)
            good = truncated_components(h, mu, u, k, 4 * X - 1)
            recovered = [sum((weight * column[n] for weight, column
                              in zip(weights, good)), Q(0))
                         for n in range(4 * X)]
            moments = []
            for slot, column in enumerate(good, 1):
                moments.append({'slot': slot, **json_exact(block_energy(column, X)),
                    'cross_with_actual': json_exact(sum(column[n] * sums[n]
                                                       for n in range(X, 2 * X))),
                    'child_cross_with_actual': json_exact(sum(column[n] * sums[n]
                                                             for n in range(2 * X, 4 * X)))})
            rows.append({'X': X, 'arity': k, 'cutoff': u,
                'cutoff_condition': (u + 1) ** k > 4 * X - 1,
                'missing': False, 'weights': [str(value) for value in weights],
                'actual_prefix_sha256': digest(sums[:4 * X]),
                'recovered_prefix_sha256': digest([int(value) for value in recovered]),
                'all_coefficients_recovered_exactly': recovered == sums[:4 * X],
                **json_exact(block_energy(sums, X)), 'component_moments': moments,
                'tuple_term_coefficient_charge': str(sum(abs(value) for value in weights)),
                'no_prime_or_factor_oracle_used': True,
                'new_actual_coefficient_holdout_claimed': False,
                'global_signed_upper_bound_proved': False})
    return {'cutoff': N, 'complete_inverse_sha256': digest(mu), 'rows': rows}


def ceiling(n, exponent):
    """Exact full rational-power ceiling, using integer comparisons only."""
    exponent = Q(exponent)
    if type(n) is not int or n < 1 or exponent < 0:
        raise ValueError('positive integer base and nonnegative exponent required')
    if n == 1 or exponent == 0:
        return 1
    integer, remainder = divmod(exponent.numerator, exponent.denominator)
    base = n ** integer
    if remainder == 0:
        return base
    if remainder == 1 and exponent.denominator >= base * (n - 1):
        # Bernoulli gives (1+1/base)**denominator >= n. Thus the
        # requested power lies strictly above base and at most base+1.
        return base + 1
    target = n ** exponent.numerator
    lo, hi = 0, 1
    while hi ** exponent.denominator < target:
        hi *= 2
    while hi - lo > 1:
        mid = (hi + lo) // 2
        if mid ** exponent.denominator < target:
            lo = mid
        else:
            hi = mid
    return hi


def potential_candidates(features, coefficient_grid, support_budget):
    programs = [{'terms': []}]
    for size in range(1, support_budget + 1):
        for support in combinations(range(len(features)), size):
            for weights in product(coefficient_grid, repeat=size):
                programs.append({'terms': [
                    {'feature': features[j], 'weight': str(Q(weight))}
                    for j, weight in zip(support, weights)]})
    return programs


def potential(program, rows, X):
    result = Q(0)
    for term in program['terms']:
        feature = term['feature']
        matches = [row for row in rows if row['X'] == X
                   and row['arity'] == feature['arity']]
        if len(matches) != 1 or matches[0].get('missing'):
            raise ValueError('potential feature has missing or duplicate actual row')
        energy = matches[0]['component_moments'][feature['slot'] - 1]['energy']
        result += Q(term['weight']) * Q(energy) / ceiling(X, feature['normalizing_power'])
    return result


def innovation(program, rows, X):
    row = next(row for row in rows if row['X'] == X and not row.get('missing'))
    return (Q(row['child_energy']) / (4 * X * X) - Q(row['energy']) / (X * X)
            + potential(program, rows, 2 * X) - potential(program, rows, X))


def fit_potential(program, rows, scales, levels):
    result = dict(program)
    fitted = {}
    for q in levels:
        maximum = max([Q(0)] + [innovation(program, rows, X) / ceiling(X, Q(1, q))
                               for X in scales])
        fitted[str(q)] = str(Q(5, 4) * maximum + Q(1, 2 ** 64))
    result['fitted_constants'] = fitted
    return result


def score_potential(program, rows, scales, levels):
    observations = []
    for X in scales:
        value = innovation(program, rows, X)
        for q in levels:
            bound = Q(program['fitted_constants'][str(q)]) * ceiling(X, Q(1, q))
            observations.append({'X': X, 'level': q,
                'signed_innovation': str(value), 'bound': str(bound),
                'margin': str(bound - value), 'finite_pass': value <= bound,
                'global_signed_upper_bound_proved': False})
    return {'observations': observations,
            'finite_passes': sum(row['finite_pass'] for row in observations),
            'finite_cases': len(observations),
            'largest_constant': str(max(Q(value) for value
                                        in program['fitted_constants'].values())),
            'global_signed_upper_bound_proved': False}


def verify_reference_records(records, specs):
    expected = [feature_table(s['seed'], s['cutoff'], s['arities'], s['indices'])
                for s in specs]
    if records != expected:
        raise AssertionError('generic reference records differ from independent replay')
    return expected


def verify_file_hashes(mapping, relative_to=None):
    for name, expected in mapping.items():
        path = Path(name)
        if not path.is_absolute() and relative_to is not None:
            path = Path(relative_to) / path
        if file_sha(path) != expected:
            raise AssertionError(f'file hash mismatch: {path}')


def read_json(path):
    return json.loads(Path(path).read_text())


def selected_potentials(program_records, validation_records, support_budget=2):
    """Replay the fixed best-per-support-size rule independently."""
    scores = {record['program_id']: record['score'] for record in validation_records}
    if len(scores) != len(validation_records):
        raise AssertionError('duplicate validation program identifiers')
    winners = []
    if type(support_budget) is not int or support_budget < 0:
        raise ValueError('nonnegative integer support budget required')
    for size in range(support_budget + 1):
        group = [record for record in program_records
                 if len(record['program']['terms']) == size]
        if not group:
            continue
        def rank(record):
            score = scores[record['program_id']]
            return (-score['finite_passes'], Q(score['largest_constant']),
                    len(str(record['program'])), record['program_id'])
        winners.append(min(group, key=rank))
    return winners


def verify_potential_programs(records, protocol, training_rows):
    """Check every dictionary/grid candidate and its frozen fitted constants."""
    candidates = potential_candidates(protocol['potential_feature_dictionary'],
                                      protocol['coefficient_grid'],
                                      protocol['support_budget'])
    if len(records) != len(candidates):
        raise AssertionError('potential candidate count differs from fixed grammar')
    expected = []
    for program in candidates:
        fitted = fit_potential(program, training_rows, protocol['training_scales'],
                               protocol['levels'])
        expected.append({'program_id': digest(fitted), 'program': fitted,
                         'training_score': score_potential(
                             fitted, training_rows, protocol['training_scales'],
                             protocol['levels'])})
    if records != expected:
        raise AssertionError('potential programs, training constants or scores differ')
    if len({record['program_id'] for record in records}) != len(records):
        raise AssertionError('duplicate potential program identifiers')
    if any(Q(term['weight']) < 0 for record in records
           for term in record['program']['terms']):
        raise AssertionError('potential dictionary has a negative square weight')
    return expected


def verify_potential_validation(records, programs, rows, scales, levels):
    expected = [{'program_id': record['program_id'], 'score': score_potential(
                 record['program'], rows, scales, levels)} for record in programs]
    if records != expected:
        raise AssertionError('potential validation scores differ from replay')
    return expected


def final_potential_result(record, rows, scales, levels):
    """Missing free level constants remain missing; no refitting is permitted."""
    program = record['program']
    observations = []
    for X in scales:
        value = innovation(program, rows, X)
        for q in levels:
            missing = str(q) not in program['fitted_constants']
            bound = None if missing else Q(program['fitted_constants'][str(q)]) * ceiling(X, Q(1, q))
            observations.append({
                'X': X, 'level': q, 'signed_innovation': str(value),
                'bound': None if missing else str(bound),
                'margin': None if missing else str(bound - value),
                'missing': missing, 'finite_pass': None if missing else value <= bound,
                'global_signed_upper_bound_proved': False,
            })
    return {'program_id': record['program_id'], 'observations': observations,
            'finite_passes': sum(row['finite_pass'] is True for row in observations),
            'finite_cases': sum(not row['missing'] for row in observations),
            'missing_cases': sum(row['missing'] for row in observations)}


def reconstruction_observations(tables, model, promotion):
    observations = []
    for table in tables:
        for row in table['rows']:
            k = row['arity']
            weights = continued_weights(model, k, promotion)
            entry = {'reference_id': row['reference_id'], 'arity': k,
                     'x': row['x'], 'u': row['u'],
                     'observed_target': row['anonymous_target']}
            if weights is None:
                entry.update({'missing': True, 'reason': 'unseen_arity_without_promotion'})
            else:
                predicted = sum((weight * Q(value) for weight, value
                                 in zip(weights, row['columns'][:k])), Q(0))
                entry.update({'predicted': str(predicted),
                              'finite_pass': predicted == Q(row['anonymous_target']),
                              'promotion_enabled': promotion})
            observations.append(entry)
    return observations


def check_generic_holdout(protocol, final_specs):
    """Reject reused generic references and response indices for final cases."""
    development = protocol['generic_training'] + protocol['generic_validation']
    old_seeds = {spec['seed'] for spec in development} | {123, 456, 789}
    pairs = {(spec['seed'], x) for spec in development for x in spec['indices']}
    for spec in final_specs:
        if spec['seed'] in old_seeds:
            raise AssertionError('final generic reference reuses a development seed')
        if any((spec['seed'], x) in pairs for x in spec['indices']):
            raise AssertionError('final generic response pair was previously seen')


def verify_actual_profile(observed, model, arities, scales=None):
    if scales is None:
        scales = list(dict.fromkeys(row['X'] for row in observed['rows']))
    expected = actual_profile(scales, arities, model)
    if observed != expected:
        raise AssertionError('actual arithmetic profile differs from independent sieve replay')
    return expected


def expanded_scales(scales):
    return sorted(set(scales) | {2 * X for X in scales} | {1, 2})


def expected_queue(protocol, model, winners, validation_results):
    scores = {row['program_id']: row['score'] for row in validation_results}
    claim = ('exists q0, every integer q>=q0, some finite C_q independent of X, '
             'every dyadic X>=1: E(2X)+V(2X)-E(X)-V(X)<=C_q ceil(X^(1/q))')
    return {'protocol_sha256': digest(protocol), 'reconstruction_inference': model,
        'potential_queue': [{'program_id': row['program_id'],
            'exact_program': row['program'], 'validation_score': scores[row['program_id']],
            'global_claim': claim, 'exact_fitted_constants_apply_only_at_stored_levels': True,
            'unseen_level_constants_are_unknown': True, 'global_bound_proved': False}
            for row in winners],
        'candidate_ids_frozen_before_final': True, 'final_data_used_for_selection': False}


def counterfeit_control(protocol, cases, cutoff):
    head = 8 * max(protocol['validation_scales'])
    if head > cutoff:
        raise AssertionError('counterfeit shared prefix exceeds final cutoff')
    mu = prime_mu(cutoff)
    fake = mu[:head + 1] + [1] * (cutoff - head)
    fake_sums = prefix(fake)
    row_sums = convolution(fake, [0] + [1] * cutoff, cutoff)
    return {'shared_actual_prefix_through': head,
        'shared_prefix_sha256': digest(mu[:head + 1]),
        'complete_fake_sha256': digest(fake), 'actual_complete_inverse': False,
        'violating_divisor_rows': sum(row_sums[n] != int(n == 1)
                                     for n in range(1, cutoff + 1)),
        'rows': [{'X': X, **json_exact(block_energy(fake_sums, X))}
                 for X in cases['actual_scales']],
        'finite_reconstruction_does_not_promote_false_inverse': True,
        'not_an_actual_RH_counterexample': True}


def verify_cases(protocol, seal_path, cases):
    design = protocol['final_design']
    seed = int(file_sha(seal_path)[:8], 16)
    specs = [{'seed': seed + j, 'cutoff': design['generic_cutoff'],
              'arities': design['arity_calibration'] + design['new_arities'],
              'indices': design['generic_indices']} for j in (31, 97)]
    expected = {'protocol_sha256': digest(protocol), 'seal_sha256': file_sha(seal_path),
        'generated_after_seal': True, 'generic_specs': specs,
        'actual_scales': design['actual_scales'], 'arities': [2, 3, 6, 7],
        'seen_levels': design['seen_levels'], 'new_levels': design['new_levels'],
        'actual_arithmetic_is_new_operator_response_not_new_coefficient_holdout': True}
    if cases != expected:
        raise AssertionError('final cases differ from the sealed deterministic design')
    check_generic_holdout(protocol, specs)
    previously_scored = (set(protocol['training_scales'])
                         | set(protocol['validation_scales'])
                         | {2 * X for X in protocol['validation_scales']})
    if set(cases['actual_scales']) & previously_scored:
        raise AssertionError('final actual operator scales reuse selected or validation scales')
    exposed = set(protocol.get('failed_final_operator_scales_excluded', []))
    if (set(cases['actual_scales']) | {2 * X for X in cases['actual_scales']}) & exposed:
        raise AssertionError('final operator responses reuse a retained failed run')
    for old in protocol.get('retained_failed_runs', []):
        failure_path = Path(old['failure_path'])
        if file_sha(failure_path) != old['failure_sha256']:
            raise AssertionError('retained failed-run record changed')
        old_path = old.get('exposed_final_cases_path')
        if old_path:
            if file_sha(old_path) != old['exposed_final_cases_sha256']:
                raise AssertionError('retained failed final cases changed')
            old_cases = read_json(old_path)
            old_pairs = {(s['seed'], s['cutoff']) for s in old_cases['generic_specs']}
            if old_pairs & {(s['seed'], s['cutoff']) for s in specs}:
                raise AssertionError('generic references reuse a retained failed run')
    if set(cases['new_levels']) & set(protocol['levels']):
        raise AssertionError('new level constants were already fitted')
    if not set(cases['seen_levels']) <= set(protocol['levels']):
        raise AssertionError('seen levels lack frozen training constants')


def normalize_denials(batch):
    """Compatibility normalization solely for worker access-denial labels."""
    batch = dict(batch)
    denials = batch['access_denials']
    labels = {'inverse_prefix_proof.txt': 'proof_file', 'route-04.json': 'route_file',
              'final_cases.json': 'final_cases', 'final_evaluation.json': 'final_evaluation'}
    batch['access_denials'] = {labels.get(Path(key).name, key): value
                              for key, value in denials.items()}
    return batch


def isolated_worker_replay(run_directory, protocol):
    base = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix='inverse-prefix-independent-replay-') as directory:
        replay = Path(directory)
        (replay / 'protocol.json').write_text(json.dumps(protocol, indent=2) + '\n')
        completed = subprocess.run(
            [sys.executable, str(base / 'inverse_prefix_search.py'), 'worker',
             '--run-dir', str(replay)], cwd=base, capture_output=True, text=True,
            check=True)
        hashes = {}
        for name in ('candidate_batch.json', 'validation.json', 'proof_queue.json'):
            original, regenerated = Path(run_directory) / name, replay / name
            if name == 'candidate_batch.json':
                left = normalize_denials(read_json(original))
                right = normalize_denials(read_json(regenerated))
                if left != right:
                    raise AssertionError('isolated candidate worker replay differs')
            elif original.read_bytes() != regenerated.read_bytes():
                raise AssertionError(f'isolated worker replay differs: {name}')
            hashes[name] = {'source_sha256': file_sha(original),
                            'replayed_sha256': file_sha(regenerated),
                            'exact_file_hash_match': file_sha(original) == file_sha(regenerated)}
        return {'files': hashes, 'only_denial_path_labels_normalized': True,
                'worker_exit_code': completed.returncode,
                'producer_math_imported_by_independent_checker': False}


def audit_run(run_directory):
    """Bind independent arithmetic to frozen run records; write no files here."""
    directory = Path(run_directory).resolve()
    base = Path(__file__).resolve().parent
    protocol = read_json(directory / 'protocol.json')
    batch = read_json(directory / 'candidate_batch.json')
    validation = read_json(directory / 'validation.json')
    queue = read_json(directory / 'proof_queue.json')
    seal = read_json(directory / 'seal.json')
    cases = read_json(directory / 'final_cases.json')
    final = read_json(directory / 'final_evaluation.json')
    groups = {}
    counts = {}
    protocol_hash = digest(protocol)
    verify_file_hashes(protocol['code_sha256'], base)
    verify_file_hashes(protocol['code_sha256'], directory / 'frozen_source')
    verify_file_hashes(protocol['source_sha256'])
    for record in (batch, validation, queue, seal, cases, final):
        if record['protocol_sha256'] != protocol_hash:
            raise AssertionError('protocol digest mismatch')
    if protocol['recurrence_feature_dictionary'] != RECURRENCE_FEATURES:
        raise AssertionError('unrecognized declared recurrence feature dictionary')
    if (protocol['global_actual_signed_innovation_bound_proved']
            or protocol['RH_proved']
            or protocol['new_actual_prime_coefficient_holdout_claimed']):
        raise AssertionError('protocol overstates arithmetic or holdout scope')
    source_round = Path(protocol['source_review_round']).resolve()
    for name in ('manifest.json', 'verification.json', 'integration_verification.json'):
        if str(source_round / name) not in protocol['source_sha256']:
            raise AssertionError('source review integrity file lacks a frozen hash')
    groups['source_code_protocol_and_frozen_integrity'] = True

    expected_seal = {'protocol_sha256': protocol_hash,
        'files': {name: file_sha(directory / name) for name in
                  ('candidate_batch.json', 'validation.json', 'proof_queue.json')},
        'selection_closed': True, 'final_cases_exist': False}
    if seal != expected_seal:
        raise AssertionError('selection seal differs from frozen worker files')
    denials = normalize_denials(batch)['access_denials']
    if denials != {'proof_file': True, 'route_file': True,
                   'final_cases': True, 'final_evaluation': True}:
        raise AssertionError('worker evidence-access restrictions were not enforced')
    groups['selection_seal_and_worker_access_denials'] = True

    training = verify_reference_records(batch['generic_training'], protocol['generic_training'])
    model = infer([row for table in training for row in table['rows']],
                  protocol['reconstruction_arities'], protocol['recurrence_support_budget'],
                  protocol['recurrence_feature_dictionary'])
    if batch['reconstruction_inference'] != model:
        raise AssertionError('sparse arity or recurrence inference differs from independent fit')
    generic_validation = verify_reference_records(validation['generic_validation'],
                                                  protocol['generic_validation'])
    if validation['reconstruction_observations'] != reconstruction_observations(
            generic_validation, model, True):
        raise AssertionError('generic validation reconstruction observations differ')
    counts['generic_training_response_rows'] = sum(len(table['rows']) for table in training)
    counts['generic_validation_response_rows'] = sum(len(table['rows']) for table in generic_validation)
    counts['arity_supports_checked'] = sum(model['arity_supports_checked'].values())
    counts['retained_recurrence_fits'] = len(model['retained_recurrence_fits'])
    groups['independent_generic_arithmetic_sparse_inference_and_recurrence'] = True

    actual_training = verify_actual_profile(batch['actual_training'], model,
        protocol['potential_arities'], expanded_scales(protocol['training_scales']))
    actual_validation = verify_actual_profile(validation['actual_validation'], model,
        protocol['potential_arities'], expanded_scales(protocol['validation_scales']))
    programs = verify_potential_programs(batch['potential_programs'], protocol, actual_training['rows'])
    validation_results = verify_potential_validation(validation['potential_results'], programs,
        actual_validation['rows'], protocol['validation_scales'], protocol['levels'])
    winners = selected_potentials(programs, validation_results, protocol['support_budget'])
    if queue != expected_queue(protocol, model, winners, validation_results):
        raise AssertionError('queue differs from support-stratified frozen selection')
    counts['potential_programs'] = len(programs)
    counts['selected_potential_programs'] = len(winners)
    counts['actual_training_profile_rows'] = len(actual_training['rows'])
    counts['actual_validation_profile_rows'] = len(actual_validation['rows'])
    groups['actual_prime_arithmetic_signed_moments_and_cross_terms'] = True
    groups['complete_potential_grammar_fitting_scoring_and_queue_selection'] = True

    verify_cases(protocol, directory / 'seal.json', cases)
    generic_final = verify_reference_records(final['generic_final'], cases['generic_specs'])
    if final['cases_sha256'] != digest(cases):
        raise AssertionError('final case digest mismatch')
    enabled = reconstruction_observations(generic_final, model, True)
    disabled = reconstruction_observations(generic_final, model, False)
    if final['reconstruction_observations'] != enabled:
        raise AssertionError('promotion-enabled final responses differ')
    if final['promotion_disabled_observations'] != disabled:
        raise AssertionError('promotion-disabled missing responses differ')
    actual_final = verify_actual_profile(final['actual_profile'], model, cases['arities'],
                                        expanded_scales(cases['actual_scales']))
    expected_results = [final_potential_result(record, actual_final['rows'],
        cases['actual_scales'], cases['seen_levels'] + cases['new_levels']) for record in winners]
    if final['potential_results'] != expected_results:
        raise AssertionError('final potential observations or unknown constants differ')
    fake = counterfeit_control(protocol, cases, actual_final['cutoff'])
    if final['counterfeit_control'] != fake or fake['violating_divisor_rows'] == 0:
        raise AssertionError('counterfeit divisor control differs or is not a false inverse')
    if final['global_actual_signed_innovation_bound_proved'] or final['RH_proved']:
        raise AssertionError('finite final evaluation claims a global theorem')
    counts['generic_final_response_rows'] = sum(len(table['rows']) for table in generic_final)
    counts['promoted_final_passes'] = sum(row.get('finite_pass', False) for row in enabled)
    counts['promotion_disabled_missing_cases'] = sum(row.get('missing', False) for row in disabled)
    counts['actual_final_profile_rows'] = len(actual_final['rows'])
    counts['actual_final_reconstruction_failures'] = sum(
        not row.get('all_coefficients_recovered_exactly', False) for row in actual_final['rows'])
    counts['potential_final_finite_cases'] = sum(row['finite_cases'] for row in expected_results)
    counts['potential_final_finite_passes'] = sum(row['finite_passes'] for row in expected_results)
    counts['potential_final_missing_cases'] = sum(row['missing_cases'] for row in expected_results)
    counts['counterfeit_divisor_violations'] = fake['violating_divisor_rows']
    groups['post_seal_fresh_generic_final_case_generation'] = True
    groups['promotion_ablation_and_actual_final_reconstruction'] = True
    groups['final_signed_potential_scores_and_unseen_level_missingness'] = True
    groups['counterfeit_scope_and_no_global_arithmetic_claim'] = True

    replay = isolated_worker_replay(directory, protocol)
    groups['isolated_model_free_worker_replay'] = True
    return {'schema': 1, 'all_passed': all(groups.values()), 'audit_groups': groups,
        'counts': counts, 'protocol_sha256': protocol_hash,
        'final_evaluation_sha256': file_sha(directory / 'final_evaluation.json'),
        'seal_sha256': file_sha(directory / 'seal.json'), 'isolated_replay': replay,
        'producer_math_imported_by_independent_checker': False,
        'global_actual_signed_innovation_bound_proved': False, 'RH_proved': False,
        'new_actual_coefficient_holdout_claimed': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run-dir', required=True, type=Path)
    args = parser.parse_args()
    result = audit_run(args.run_dir)
    with (args.run_dir / 'verification.json').open('x') as output:
        output.write(json.dumps(result, indent=2) + '\n')
    print('Independent inverse-prefix audit passed: '
          f'{len(result["audit_groups"])} groups; counts={result["counts"]}', flush=True)


if __name__ == '__main__':
    main()
