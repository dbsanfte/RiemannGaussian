#!/usr/bin/env python3
"""Learn compressed inverse representations and signed scale-potential leads."""
import argparse
import builtins
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from fractions import Fraction as Q
import inverse_prefix_grammar as g

BASE = Path(__file__).resolve().parent
CODE = ['inverse_prefix_grammar.py', 'inverse_prefix_search.py', 'inverse_prefix_analytic.py',
        'inverse_prefix_report.py', 'inverse_prefix_proof.txt', 'check_inverse_prefix_math.py',
        'check_inverse_prefix_search.py', 'check_inverse_prefix_analytic.py',
        'test_inverse_prefix_contracts.py', 'plot_inverse_prefix.py']
SEALED = ['candidate_batch.json', 'validation.json', 'proof_queue.json']


def read(p):
    return json.loads(Path(p).read_text())


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def write(p, v):
    Path(p).write_text(json.dumps(v, indent=2) + '\n')


def expanded_scales(scales):
    return sorted(set(scales) | {2 * X for X in scales} | {1, 2})


def key(program, score):
    return (-score['finite_passes'], Q(score['largest_constant']),
            len(str(program['program'])), program['program_id'])


def observation(tables, model, promotion):
    result = []
    for table in tables:
        for row in table['rows']:
            k = row['arity']
            weights = g.continued_weights(model, k) if promotion or str(k) in model['coefficient_table'] else None
            entry = {n: row[n] for n in ['reference_id', 'arity', 'x', 'u']}
            entry['observed_target'] = row['anonymous_target']
            if weights is None:
                entry.update({'missing': True, 'reason': 'unseen_arity_without_promotion'})
            else:
                predicted = sum((c * v for c, v in zip(weights, row['columns'][:k])), Q(0))
                entry.update({'predicted': str(predicted), 'finite_pass': predicted == row['anonymous_target'],
                              'promotion_enabled': promotion})
            result.append(entry)
    return result


def worker(d):
    d = Path(d).resolve()
    spec = read(d / 'protocol.json')
    # After importing the declared modules, restrict the model-free learner to
    # its protocol and output files. Past reports/proofs and final cases are
    # actively denied, rather than merely marked as unavailable in metadata.
    allowed = {d / 'protocol.json'} | {d / n for n in SEALED}
    original_open, original_io_open = builtins.open, __import__('io').open
    original_path_open = Path.open
    def guarded(file, *args, **kwargs):
        if isinstance(file, (str, Path)) and Path(file).resolve() not in allowed:
            raise PermissionError('Discovery worker cannot read external evidence or final cases')
        return original_open(file, *args, **kwargs)
    builtins.open = guarded
    __import__('io').open = guarded
    # Python 3.10 pathlib caches its own io.open accessor, so patching io.open
    # alone does not cover Path.read_text/read_bytes.
    def guarded_path_open(path, *args, **kwargs):
        if path.resolve() not in allowed:
            raise PermissionError('Discovery worker cannot read external evidence or final cases')
        return original_path_open(path, *args, **kwargs)
    Path.open = guarded_path_open
    denials = {}
    for label, name in [('proof_file', BASE / 'inverse_prefix_proof.txt'),
                        ('route_file', BASE / 'candidate-review-results/sol-6.1-proof-routes-001/route-04.json'),
                        ('final_cases', d / 'final_cases.json'), ('final_evaluation', d / 'final_evaluation.json')]:
        try:
            read(name)
            denials[label] = False
        except PermissionError:
            denials[label] = True
    training = [g.feature_table(s['seed'], s['cutoff'], s['arities'], s['indices'])
                for s in spec['generic_training']]
    rows = [r for table in training for r in table['rows']]
    model = g.infer(rows, spec['reconstruction_arities'], spec['recurrence_support_budget'])
    actual = g.actual_profile(expanded_scales(spec['training_scales']), spec['potential_arities'], model)
    templates = g.potential_candidates(spec['potential_feature_dictionary'], spec['coefficient_grid'], spec['support_budget'])
    programs = []
    for p in templates:
        p = g.fit_potential(p, actual['rows'], spec['training_scales'], spec['levels'])
        programs.append({'program_id': g.digest(p), 'program': p,
            'training_score': g.score_potential(p, actual['rows'], spec['training_scales'], spec['levels'])})
    batch = {'protocol_sha256': g.digest(spec), 'access_denials': denials,
             'generic_training': training, 'reconstruction_inference': model,
             'actual_training': actual, 'potential_programs': programs}
    write(d / 'candidate_batch.json', batch)
    generic_validation = [g.feature_table(s['seed'], s['cutoff'], s['arities'], s['indices'])
                          for s in spec['generic_validation']]
    validation_actual = g.actual_profile(expanded_scales(spec['validation_scales']), spec['potential_arities'], model)
    results = [{'program_id': p['program_id'], 'score': g.score_potential(p['program'], validation_actual['rows'],
               spec['validation_scales'], spec['levels'])} for p in programs]
    validation = {'protocol_sha256': g.digest(spec), 'generic_validation': generic_validation,
        'reconstruction_observations': observation(generic_validation, model, True),
        'actual_validation': validation_actual, 'potential_results': results}
    write(d / 'validation.json', validation)
    scores = {r['program_id']: r['score'] for r in results}
    selected = []
    for size in range(spec['support_budget'] + 1):
        eligible = [p for p in programs if len(p['program']['terms']) == size]
        if eligible:
            p = min(eligible, key=lambda p: key(p, scores[p['program_id']]))
            selected.append({'program_id': p['program_id'], 'exact_program': p['program'],
                'validation_score': scores[p['program_id']],
                'global_claim': 'exists q0, every integer q>=q0, some finite C_q independent of X, every dyadic X>=1: E(2X)+V(2X)-E(X)-V(X)<=C_q ceil(X^(1/q))',
                'exact_fitted_constants_apply_only_at_stored_levels': True,
                'unseen_level_constants_are_unknown': True, 'global_bound_proved': False})
    write(d / 'proof_queue.json', {'protocol_sha256': g.digest(spec), 'reconstruction_inference': model,
        'potential_queue': selected, 'candidate_ids_frozen_before_final': True, 'final_data_used_for_selection': False})
    builtins.open, __import__('io').open = original_open, original_io_open
    Path.open = original_path_open
    print(f'Learned {len(model["learned_vectors"])} reconstruction rows; retained '
          f'{len(model["retained_recurrence_fits"])} recurrence fits; evaluated {len(programs)} potential programs.', flush=True)


def specification():
    from candidate_review_report import load_latest
    review = load_latest()
    if review['status'] == 'not_run':
        raise ValueError('Complete independent parallel candidate review before this stage')
    routes = BASE / 'candidate-review-results/sol-6.1-proof-routes-001'
    source_files = [Path(review['round_directory']) / n for n in ['manifest.json', 'verification.json', 'integration_verification.json']]
    source_files += [routes / n for n in ['route-01.json', 'route-02.txt', 'route-03.json', 'route-04.json', 'route-05.txt']]
    preflight = BASE / 'inverse-prefix-results/development-preflight-001'
    source_files += [preflight / 'record.json', preflight / 'inverse_prefix_grammar.py']
    retained_failures, excluded_scales = [], set()
    for failure in sorted((BASE / 'inverse-prefix-results').glob('*/failure.json')):
        source_files.append(failure)
        item = {'failure_path': str(failure), 'failure_sha256': sha(failure)}
        cases_path = failure.parent / 'final_cases.json'
        if cases_path.exists():
            old_cases = read(cases_path)
            source_files.append(cases_path)
            excluded_scales.update(expanded_scales(old_cases['actual_scales']))
            item['exposed_final_cases_path'] = str(cases_path)
            item['exposed_final_cases_sha256'] = sha(cases_path)
        retained_failures.append(item)
    retry_index = 0
    while True:
        fresh_scales = [1001 + 109 * retry_index,
                        2 ** (10 + 4 * retry_index), 2 ** (11 + 4 * retry_index),
                        2 ** (12 + 4 * retry_index)]
        if not (set(fresh_scales) | {2 * X for X in fresh_scales}) & excluded_scales:
            break
        retry_index += 1
    arities = [1, 2, 3, 4, 5]
    return {'grammar_version': g.VERSION, 'code_sha256': {n: sha(BASE / n) for n in CODE},
        'source_sha256': {str(p): sha(p) for p in source_files},
        'source_review_round': review['round_directory'],
        'generic_training': [{'seed': seed, 'cutoff': 96, 'arities': arities, 'indices': [4, 9, 15, 27, 43, 71, 91]} for seed in [92811, 177241, 661879]],
        'generic_validation': [{'seed': seed, 'cutoff': 160, 'arities': arities, 'indices': [6, 17, 33, 59, 101, 157]} for seed in [881921, 923711]],
        'reconstruction_arities': arities, 'recurrence_feature_dictionary': g.RECURRENCE_FEATURES,
        'recurrence_support_budget': 3, 'potential_arities': [2, 3],
        'training_scales': [16, 32, 64, 128], 'validation_scales': [192, 256, 384],
        'levels': [2, 3, 6, 12], 'potential_feature_dictionary': g.potential_dictionary(),
        'coefficient_grid': ['1/4', '1', '4'], 'support_budget': 2,
        'selection': 'best per support size by validation passes, exact largest fitted constant, description length, stable id',
        'generic_inputs_are_anonymous_unrelated_references': True,
        'expected_reconstruction_or_recurrence_coefficients_supplied': False,
        'nonnegative_potential_features_and_proof_methods_are_supplied_assumptions': True,
        'learner_reads_analytic_candidates_or_final_cases': False,
        'actual_coefficient_overlap_with_previous_development': True,
        'new_actual_prime_coefficient_holdout_claimed': False,
        'fresh_generic_reference_and_operator_responses_required': True,
        'retained_failed_runs': retained_failures,
        'failed_final_operator_scales_excluded': sorted(excluded_scales),
        'final_scale_retry_index': retry_index,
        'final_scale_design_visible_to_worker_but_responses_withheld': True,
        'search_resource_missingness_not_generalized_beyond_native_pilot_budget': True,
        'full_rational_power_ceiling_semantics': True,
        'semantic_rational_denominator_or_integer_arity_cap': False,
        'native_rational_power_bit_budget': 1000000,
        'final_design': {'arity_calibration': [2], 'new_arities': [6, 7],
            'generic_indices': [11, 23, 53, 89, 131, 191, 257], 'generic_cutoff': 272,
            'actual_scales': fresh_scales, 'seen_levels': [3, 12], 'new_levels': [13, 17]},
        'global_actual_signed_innovation_bound_proved': False, 'RH_proved': False}


def final(d):
    d = Path(d)
    spec, seal, queue = map(read, [d / 'protocol.json', d / 'seal.json', d / 'proof_queue.json'])
    for n, h in seal['files'].items():
        assert sha(d / n) == h
    f = spec['final_design']
    seed = int(sha(d / 'seal.json')[:8], 16)
    final_specs = [{'seed': seed + j, 'cutoff': f['generic_cutoff'],
                    'arities': f['arity_calibration'] + f['new_arities'], 'indices': f['generic_indices']} for j in [31, 97]]
    cases = {'protocol_sha256': g.digest(spec), 'seal_sha256': sha(d / 'seal.json'),
        'generated_after_seal': True, 'generic_specs': final_specs,
        'actual_scales': f['actual_scales'], 'arities': [2, 3, 6, 7],
        'seen_levels': f['seen_levels'], 'new_levels': f['new_levels'],
        'actual_arithmetic_is_new_operator_response_not_new_coefficient_holdout': True}
    write(d / 'final_cases.json', cases)
    tables = [g.feature_table(s['seed'], s['cutoff'], s['arities'], s['indices']) for s in final_specs]
    model = queue['reconstruction_inference']
    profile = g.actual_profile(expanded_scales(cases['actual_scales']), cases['arities'], model)
    results = []
    for row in queue['potential_queue']:
        p, observations = row['exact_program'], []
        for X in cases['actual_scales']:
            value = g.innovation(p, profile['rows'], X)
            for q in cases['seen_levels'] + cases['new_levels']:
                missing = str(q) not in p['fitted_constants']
                bound = None if missing else Q(p['fitted_constants'][str(q)]) * g.ceiling(X, Q(1, q))
                observations.append({'X': X, 'level': q, 'signed_innovation': str(value),
                    'bound': None if missing else str(bound), 'margin': None if missing else str(bound - value),
                    'missing': missing, 'finite_pass': None if missing else value <= bound,
                    'global_signed_upper_bound_proved': False})
        results.append({'program_id': row['program_id'], 'observations': observations,
            'finite_passes': sum(v['finite_pass'] is True for v in observations),
            'finite_cases': sum(not v['missing'] for v in observations), 'missing_cases': sum(v['missing'] for v in observations)})
    # A fake tail agreeing with all discovery coefficients must still fail the
    # complete inverse condition. Low-prefix reconstruction does not validate it.
    N = profile['cutoff']; head = 8 * max(spec['validation_scales'])
    mu = g.inverse([0] + [1] * N)
    fake = mu[:head + 1] + [1] * (N - head)
    fake_M = g.prefix(fake)
    counterfeit = {'shared_actual_prefix_through': head, 'shared_prefix_sha256': g.digest(mu[:head + 1]),
        'complete_fake_sha256': g.digest(fake), 'actual_complete_inverse': False,
        'violating_divisor_rows': sum(v != int(n == 1) for n, v in enumerate(g.convolution(fake, [0] + [1] * N, N)) if n),
        'rows': [{'X': X, **g.block_energy(fake_M, X)} for X in cases['actual_scales']],
        'finite_reconstruction_does_not_promote_false_inverse': True, 'not_an_actual_RH_counterexample': True}
    write(d / 'final_evaluation.json', {'protocol_sha256': g.digest(spec), 'cases_sha256': g.digest(cases),
        'generic_final': tables, 'reconstruction_observations': observation(tables, model, True),
        'promotion_disabled_observations': observation(tables, model, False),
        'actual_profile': profile, 'potential_results': results, 'counterfeit_control': counterfeit,
        'global_actual_signed_innovation_bound_proved': False, 'RH_proved': False})


def run(d):
    d = Path(d).resolve()
    d.mkdir(parents=True, exist_ok=False)
    spec = specification()
    write(d / 'protocol.json', spec)
    (d / 'frozen_source').mkdir()
    for n in CODE:
        (d / 'frozen_source' / n).write_bytes((BASE / n).read_bytes())
    try:
        subprocess.run([sys.executable, str(BASE / 'inverse_prefix_search.py'), 'worker', '--run-dir', str(d)], cwd=BASE, check=True)
        write(d / 'seal.json', {'protocol_sha256': g.digest(spec), 'files': {n: sha(d / n) for n in SEALED},
            'selection_closed': True, 'final_cases_exist': False})
        final(d)
        subprocess.run([sys.executable, str(BASE / 'check_inverse_prefix_search.py'), '--run-dir', str(d)], cwd=BASE, check=True)
        subprocess.run([sys.executable, str(BASE / 'inverse_prefix_analytic.py'), '--run-dir', str(d)], cwd=BASE, check=True)
        from inverse_prefix_report import summary, text_report
        s = summary(d)
        write(d / 'summary.json', s); (d / 'report.txt').write_text(text_report(s))
        write(BASE / 'inverse-prefix-results/latest.json', {'run_directory': str(d)})
    except Exception as exc:
        write(d / 'failure.json', {'error': str(exc), 'files_sha256': {str(p.relative_to(d)): sha(p) for p in d.rglob('*') if p.is_file()},
                                 'not_fresh_validation_for_any_later_revised_run': True})
        raise


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=['run', 'worker'])
    p.add_argument('--run-dir', required=True, type=Path)
    args = p.parse_args()
    (run if args.command == 'run' else worker)(args.run_dir)
