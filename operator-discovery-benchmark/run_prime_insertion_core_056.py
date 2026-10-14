"""Search and independently check integral bounds and inferred operator words."""
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
import resource
import time

import run_prime_insertion_055 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt
import prime_insertion_core_search_056 as SEARCH

ROOT = Path(__file__).resolve().parent
OUT = PRIOR.OUT/'core_followup_001'
FILES = ['prime_insertion_core_search_056.py', 'test_prime_insertion_core_search_056.py',
    'prime_insertion_core_search_056_development.json', 'check_prime_insertion_core_056.py',
    'test_check_prime_insertion_core_056.py', 'check_prime_insertion_core_056_development.json',
    'PRIME_INSERTION_CORE_CHECK_SCOPE_056.txt', 'PRIME_INSERTION_CORE_REVIEW_056.txt',
    'PRIME_INSERTION_EULER_BRIDGE_AUDIT_056.txt', 'run_prime_insertion_core_056.py',
    'test_prime_insertion_core_runner_056.py', 'prime_insertion_core_runner_056_development.json',
    'prime_insertion_core_protocol_056.txt']


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in snapshots):
        raise ValueError('preserve every frozen055 source')
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['uniform_target_bound_proved'] is not False or report['RH_proved'] is not False:
        raise ValueError('preserve finite055 and partial-tail scope')
    return counts+[len(snapshots)]


def validate_verification(value, field):
    if value.get('verified') is not True or value.get(field) is not True:
        raise ValueError('independent proof rule must verify its declared scope')
    if value.get('RH_proved') is not False:
        raise ValueError('partial proof cannot close RH')
    for key in ['low_core_bound_proved', 'complete_target_bound_proved', 'full_kernel_cancellation_proved']:
        if key in value and value[key] is not False: raise ValueError('unpaid full source scope')


def verify_relation_archive(archive, checker, checker_meter, search_meter):
    for row in archive['rows']:
        checked = checker.verify_first_jet(row['request'], row['certificate'], checker_meter)
        validate_verification(checked, 'first_jet_identity_proved')
        row['verification'] = checked; row['independently_verified'] = True
        request = row['request']
        word = SEARCH.factor_boolean_word(request['features'], request['coefficients'], search_meter)
        row['operator_word'] = word
        row['operator_identity_checked'] = (word is not None and
            SEARCH.verify_boolean_word(request['features'], request['coefficients'], word, search_meter))
    return dict(Counter(row['verification']['status'] for row in archive['rows']))


def insertion_words(archive):
    words = {}
    for row in archive['rows']:
        word = row['operator_word']
        if word is not None and row['operator_identity_checked'] and word['E_primes'] and not word['D_primes']:
            key = tuple(word['E_primes'])
            words[key] = {'primes': list(key), 'coefficients': row['request']['coefficients'],
                'features': row['request']['features'], 'origin': row['origin'],
                'first_jet_status': row['verification']['status'], 'operator_word': word}
    return [words[key] for key in sorted(words)]


def signed_tail_recovery(word, selected_tails):
    """Retain every coefficient in the exact Boolean expansion."""
    by_feature = {tuple(row['request']['primes']): row for row in selected_tails}
    total, tau, terms = Q(0), None, []
    for feature, coefficient in zip(word['features'], word['coefficients']):
        coefficient = Q(coefficient)
        if not coefficient: continue
        row = by_feature.get(tuple(feature))
        if row is None or not row['independently_verified']: raise ValueError('every word term needs a paid tail')
        cutoff = row['request']['tau']
        if tau is not None and cutoff != tau: raise ValueError('a common split boundary is required')
        tau = cutoff; upper = row['verification']['upper_bound']
        if Q(upper['N_power']) > Q(1, 2): raise ValueError('tail growth must meet target')
        cost = abs(coefficient)*(Q(upper['constant'])+2*Q(upper['log_coefficient']))
        total += cost
        terms.append({'primes': feature, 'coefficient': str(coefficient), 'sqrt_constant_contribution': str(cost)})
    return {'tau': tau, 'uniform_sqrt_constant': str(total), 'terms': terms,
        'recovery': 'exact Boolean word identity followed by triangle inequality',
        'tail_bound_proved': True, 'full_source_bound_proved': False}


def main():
    import check_prime_insertion_core_056 as CHECK
    started = time.monotonic()
    if OUT.exists(): raise FileExistsError('preserve every completed or failed056 study')
    counts = validate_parent()
    development_operations = sum(check_receipt(json.loads((ROOT/name).read_text()))
        for name in FILES if name.endswith('_development.json'))
    source_protocol = json.loads((PRIOR.OUT/'protocol.json').read_text())
    alpha, features = source_protocol['alpha'], source_protocol['features']
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items(): (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', {'alpha': alpha, 'features': features,
            'target_growth': {'N_power': '1/2', 'log_power': '0'},
            'tail_cutoffs': {'max_denominator': 12, 'maximum': '2'},
            'microscopic_exponents': {'max_denominator': 24, 'maximum': '2'},
            'source_values_read': False, 'new_numerical_study': False,
            'relation_solver': 'exact RREF; outside class and full prime-class table',
            'composition': 'basis promotion and pairwise sum/difference; all Boolean word factorizations',
            'ablation': 'same grammar with relation promotion disabled; actual costs reported separately',
            'aggregate_memory_limit_bytes': 16*1024**3, 'seconds_per_module': 600,
            'old_suites_or_studies_replayed': False, 'hashes_used': False,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES)})
        emit('core_proof_search_protocol_frozen', features=len(features))
        sm, bm = SEARCH.Meter(), SEARCH.Meter()
        cm = CHECK.Meter(cap=200_000_000, seconds=600)
        cutoffs = SEARCH.cutoff_grammar(12, '2', sm)
        tails = SEARCH.search_cutoffs(alpha, features, cutoffs, '1/2', meter=sm)
        for row in tails['rows']:
            checked = CHECK.verify_tail_bound(row['request'], row['certificate'], cm)
            validate_verification(checked, 'tail_bound_proved')
            row['verification'] = checked; row['independently_verified'] = True
        write(OUT/'tail_search.json', tails)
        recoveries = []
        for row in tails['selected']:
            request = {'tail_request': row['request'], 'log_power': '0'}
            certificate = SEARCH.recovery_schema_certificate(request, sm)
            checked = CHECK.verify_low_core_recovery_schema(request, certificate, cm)
            if checked.get('verified') is not True or checked['low_core_bound_proved'] is not False:
                raise ValueError('conditional implication with unpaid core required')
            recoveries.append({'request': request, 'certificate': certificate, 'verification': checked})
        write(OUT/'conditional_recovery.json', {'rows': recoveries, 'core_bound_proved': False})
        baseline = SEARCH.search_relations(features, promotion=False, meter=bm)
        enabled = SEARCH.search_relations(features, promotion=True, meter=sm)
        baseline_counts = verify_relation_archive(baseline, CHECK, cm, bm)
        enabled_counts = verify_relation_archive(enabled, CHECK, cm, sm)
        write(OUT/'relations_baseline.json', baseline)
        write(OUT/'relations_promoted.json', enabled)
        words = insertion_words(enabled)
        gammas = SEARCH.cutoff_grammar(24, '2', sm)
        microscopic = SEARCH.search_microscopic(alpha, words, gammas, '1/2', sm)
        for row in microscopic['rows']:
            checked = CHECK.verify_microscopic_bound(row['request'], row['certificate'], cm)
            validate_verification(checked, 'near_zero_bound_proved')
            row['verification'] = checked; row['independently_verified'] = True
        write(OUT/'microscopic_search.json', microscopic)
        candidates = []
        for row in microscopic['selected']:
            word = next(word for word in words if word['primes'] == row['request']['primes'])
            tail = signed_tail_recovery(word, tails['selected'])
            candidates.append({'source_word': word, 'microscopic_bound': row, 'tail_bound': tail,
                'middle_obligation': {'alpha': alpha, 'primes': word['primes'],
                    'lower_endpoint': {'formula': 'min(1/2,N^-gamma)', 'gamma': row['request']['gamma']},
                    'upper_endpoint': tail['tau'],
                    'integrand': 'h_E_R(N,t)=sum_j[2,-3,1]_j*sum_(2<=n<=2^j*N)prod_(p|Rn)(1-p^-t)',
                    'normalization': 'integrate t^(-alpha-1)/(alpha*I_alpha)',
                    'requested_bound': '|middle_R(N)|<=C_R*sqrt(N) for EVERY integer N>=2',
                    'constant_quantifier': 'there exists finite C_R independent of N', 'status': 'OPEN'},
                'analytic_RH_bridge': {'status': 'separately reviewed conditional theorem',
                    'reviews': ['PRIME_INSERTION_CORE_REVIEW_056.txt', 'PRIME_INSERTION_EULER_BRIDGE_AUDIT_056.txt'],
                    'executable_bridge_certificate': False, 'uniform_arithmetic_premise_proved': False},
                'full_source_bound_proved': False, 'RH_proved': False})
        write(OUT/'next_search_input.json', {'schema': 'prime-insertion-moving-middle-feedback-v1',
            'candidates': candidates,
            'original_target_alternative': {'source': 'empty insertion t0',
                'unpaid': 'uniform low-core integral below the automatically selected cutoff',
                'conditional_recovery': 'conditional_recovery.json'},
            'middle_not_replaced_by_first_jet': True,
            'full_source_bound_proved': False, 'RH_proved': False})
        validate_parent()
        if any((ROOT/name).read_bytes() != data for name, data in snapshots.items()):
            raise ValueError('056 sources changed after freeze')
        report = {'status': 'PROVED_COMPONENTS_AND_DISCOVERED_WORDS_MIDDLE_BOUND_OPEN',
            'tail_bound_programs_checked': len(tails['rows']),
            'selected_tail_cutoffs': [row['request'] for row in tails['selected']],
            'baseline_relation_statuses': baseline_counts, 'promoted_relation_statuses': enabled_counts,
            'learned_insertion_operators': [word['primes'] for word in words],
            'microscopic_bound_programs_checked': len(microscopic['rows']),
            'selected_microscopic_exponents': [row['request'] for row in microscopic['selected']],
            'open_middle_obligations': len(candidates),
            'development_operations': development_operations,
            'enabled_search_operations': sm.operations, 'baseline_search_operations': bm.operations,
            'independent_checker_operations': cm.operations,
            'source_values_evaluated': 0, 'numerical_integrals_evaluated': 0,
            'elapsed_seconds': time.monotonic()-started,
            'parent_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'aggregate_memory_limit_bytes': 16*1024**3,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'hashes_used': False, 'old_suites_or_studies_replayed': False,
            'first_jet_is_full_source_bound': False,
            'full_source_bound_proved': False, 'RH_proved': False, 'RH_refuted': False}
        write(OUT/'report.json', report)
        emit('core_proof_search_completed', tails=len(tails['rows']),
            microscopic=len(microscopic['rows']), open_middle_obligations=len(candidates))
        return report
    except BaseException as exc:
        write(OUT/'failure.json', {'type': type(exc).__name__, 'message': str(exc),
            'elapsed_seconds': time.monotonic()-started, 'source_values_evaluated': 0,
            'full_source_bound_proved': False, 'RH_proved': False})
        raise


if __name__ == '__main__':
    main()
