"""Freeze and verify actual-Mobius sparse inverse and uniform tail rules."""
import os
for _thread_variable in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_thread_variable] = '1'

from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_sparse_prefix_066 as SEARCH
import check_mobius_sparse_prefix_066 as CHECK
import run_mobius_walsh_energy_065 as PRIOR
import run_mobius_prefix_repair_063 as RAW
from run_fractional_prime_kernel_051 import write, emit, check_receipt

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT/'sparse_prefix_followup_001'
FILES = ['mobius_sparse_prefix_066.py', 'test_mobius_sparse_prefix_066.py',
         'mobius_sparse_prefix_search_066_development.json', 'check_mobius_sparse_prefix_066.py',
         'test_check_mobius_sparse_prefix_066.py', 'mobius_sparse_prefix_checker_066_development.json',
         'MOBIUS_SPARSE_PREFIX_CHECK_SCOPE_066.txt', 'MOBIUS_COMPLEMENTARY_CONVOLUTION_REVIEW_066.txt',
         'run_mobius_sparse_prefix_066.py', 'mobius_sparse_prefix_protocol_066.txt']
SPEC = {'cases': 'all36 saved063 RAW repairs, separately from previously selected core fills',
        'construction': 'six full-floor atoms plus signed complementary prefix indicators, then complete actual Mobius convolution',
        'actual_arithmetic_radius': 'D=floor(4N/p), possibly larger than old B=max(H,floor(y/(H+1)))',
        'new_masked_signed_source_prefix_values': False, 'new_ordinary_mu_evaluation_through_D': True,
        'new_unmasked_source_inverse_replay': True,
        'tail_bounds': 'every integer J=1..H; no head omission',
        'selected_tail_fractions': ['1/8', '1/4', '1/2', '3/4', '1'],
        'diagnostic_blocks': '[2^k,min(2^(k+1)-1,H)]',
        'workers': 3, 'native_threads_per_worker': 1, 'maximum_aggregate_bytes': 16*1024**3,
        'work_cap_per_meter': 300_000_000_000, 'module_seconds': 7200,
        'uniform_full_bound_claim': False, 'hashes_used': False}


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve065 '+name)
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['exact_energy_certificates_independently_verified'] != 324 or report['RH_proved']:
        raise ValueError('completed065 and open arithmetic bound')
    probe = PRIOR.OUT/'moment_diagnostic_001'
    names = ['mobius_walsh_moment_probe_065.py', 'test_mobius_walsh_moment_probe_065.py',
             'mobius_walsh_moment_probe_065_development.json', 'mobius_walsh_moment_probe_protocol_065.txt',
             'MOBIUS_WALSH_UNIFORM_PREFACTOR_REVIEW_065.txt']
    if sorted(p.name for p in (probe/'source_snapshot').iterdir()) != sorted(names):
        raise ValueError('complete065 diagnostic snapshot')
    for name in names:
        if (ROOT/name).read_bytes() != (probe/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve065 diagnostic '+name)
    return counts+[len(PRIOR.FILES), len(names)]


def bind_raw(saved):
    candidates = [c for c in saved['candidates'] if c['rule'] == 'raw']
    if len(candidates) != 1:
        raise ValueError('one original raw repair')
    chosen = candidates[0]
    repair, full = chosen['repair'], chosen['completion']
    rp, wp = chosen['repair_verification'], chosen['whole_verification']
    if not rp['verified'] or not rp['repair_identity_proved'] or not wp['verified'] or not wp['finite_prefix_bound_proved']:
        raise ValueError('both saved raw source admissions')
    for key in ('N', 'y', 'H'):
        if full[key] != saved[key] or wp[key] != saved[key]:
            raise ValueError('same raw source parameters')
    if repair['H'] != saved['H'] or rp['H'] != saved['H'] or repair['rule'] != 'raw' or rp['rule'] != 'raw':
        raise ValueError('raw rather than filled inverse')
    if full['parameters'] != wp['parameters'] or repair['primes'] != full['parameters']['primes'] or rp['primes'] != repair['primes']:
        raise ValueError('same arithmetic source mask')
    if full['horizons'] != wp['horizons'] or full['ratios'] != wp['ratios'] or repair['coefficient_l1'] != rp['coefficient_l1']:
        raise ValueError('same full horizons and exact prices')
    long = []
    for e, coefficients in enumerate(full['coefficients']):
        costs = wp['endpoint_costs'][e]
        values = {j: Q(c) for j, c in zip(full['horizons'], coefficients)}
        if [str(values.get(j, Q(0))) for j in range(1, saved['H']+1)] != repair['coefficients'][e]:
            raise ValueError('same source raw short coefficients')
        L = sum((abs(c) for j, c in values.items() if j > saved['H']), Q(0))
        if Q(costs['short_residual_l1']) or str(L+Q(repair['coefficient_l1'][e])) != costs['total']:
            raise ValueError('complete raw long plus short budget')
        long.append(L)
    if str(max(L+Q(v) for L, v in zip(long, repair['coefficient_l1']))) != full['budget'] or full['budget'] != wp['budget']:
        raise ValueError('same whole raw budget')
    return chosen, long


def evaluate_task(name):
    started = time.monotonic()
    saved = json.loads((RAW.OUT/name).read_text())
    old, long = bind_raw(saved)
    meter = SEARCH.Meter(cap=SPEC['work_cap_per_meter'], seconds=SPEC['module_seconds'])
    cm = CHECK.Meter(cap=SPEC['work_cap_per_meter'], seconds=SPEC['module_seconds'])
    cert = SEARCH.construct(saved['N'], saved['y'], saved['H'], old['completion']['parameters'], meter)
    verdict = CHECK.verify_sparse(cert, cm)
    if not verdict['verified']:
        raise ValueError('new sparse inverse independent admission')
    for e, endpoint in enumerate(cert['endpoints']):
        if [r['coefficient'] for r in endpoint['rows']] != old['repair']['coefficients'][e]:
            raise ValueError('large-index linear inverse equals saved small-index quadratic RAW repair')
        if endpoint['coefficient_l1'] != old['repair']['coefficient_l1'][e]:
            raise ValueError('same raw price')
    H = saved['H']
    locations = SEARCH.selected_cutoffs(H, SPEC['selected_tail_fractions'])
    selected_tails = []
    for location in locations:
        J = location['J']
        selected_tails.append({**location, 'endpoints': [e['tail_bounds'][J-1] for e in cert['endpoints']],
                               'unpaid_head_support': [1, J-1], 'actual_head_variations': [
                                   str(Q(e['coefficient_l1'])-Q(e['tail_bounds'][J-1]['actual_variation'])) for e in cert['endpoints']]})
    return {'source_raw_file': name, 'N': saved['N'], 'y': saved['y'], 'H': H, 'theta': saved['theta'],
            'parameters': old['completion']['parameters'], 'certificate': cert, 'verification': verdict,
            'same_saved_raw_source_admission_reused': True,
            'reused_raw_repair_verification': old['repair_verification'], 'reused_raw_whole_verification': old['whole_verification'],
            'raw_coefficients_match_at_every_row': True, 'previous_selected_fill': saved['selected_rule'],
            'comparison_is_raw_only': True, 'long_endpoint_l1': list(map(str, long)),
            'old_raw_whole_budget': old['completion']['budget'],
            'old_query_radius': max(H, saved['y']//(H+1)), 'new_arithmetic_radius': 4*saved['N']//old['completion']['parameters']['p'],
            'selected_tails': selected_tails, 'block_moments': SEARCH.block_moments(cert),
            'producer_operations': meter.operations, 'checker_operations': cm.operations,
            'prospective_algorithm_bytes': meter.peak_bytes_estimate,
            'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'elapsed_seconds': time.monotonic()-started,
            'uniform_full_variation_bound_proved': False, 'RH_proved': False}


def feedback(results):
    return {'schema': 'mobius-sparse-prefix-bound-feedback-v1',
            'previous_goal_turn': '065 substantive: verified energy bounds, paid prefactor, and actual block-moment diagnostic',
            'current_goal_turn': '066 actual-Mobius convolution contraction and uniform raw tail bound',
            'construction': 'six full floors plus a signed sparse list of complementary tail indicators; invert using ordinary mu*One=delta_1',
            'source_scope': 'RAW inverse branch only; not the earlier selected finite core fill',
            'uniform_tail_rule': {
                'variables': 'every N>=2,1<=y<=D=floor(4N/p),1<=J<=H<=D,r in[p/q,1]',
                'formula': 'sum_(j=J)^H |c_j| <= floor_L1 + M1/J',
                'M1': 'sum_(coalesced signed steps T)|a_T|*T',
                'explicit_bound': 'floor_L1<=6(1+r); M1<=12(1/p+r/q)*N*(2+log(max(1,D/(y+1))))',
                'square_root_tail': 'J>=c*sqrt(N), c>0 fixed, implies O_c(sqrt(N)*log(2N)) uniformly in every prefix',
                'proof_inputs': ['complete actual Mobius/floor contraction', 'signed dictionary coalescing', 'disjoint-window telescoping', '|mu(n)|<=1', 'elementary harmonic upper bound'],
                'no_new_prime_distribution_theorem': True},
            'next_obligation': {
                'declared_branch': 'H=floor(sqrtN), raw fill, J=max(1,ceil(H/2)); same p3,q5 source',
                'unpaid_expression': 'sum_(1<=j<J) |d_j+sum_T a_T*(M(floor(T/j))-M(floor(T/(j+1))))|',
                'required_rate': 'O_epsilon(N^(1/2+epsilon)) for every epsilon>0, every required prefix, both ratio endpoints',
                'actual_prime_arithmetic': 'ordinary mu through current-scale moving intervals; shared values in both channels and all rows',
                'allowed_auxiliary_controls': ['block moments with separately paid prefactors', 'signed interval pairings', 'complete convolution contractions', 'scale recurrences with paid initial and increment estimates'],
                'moment_scope': 'a block square-moment condition is sufficient only; no random-sign strength is declared necessary',
                'circularity_guard': 'a new interval, correlation, or recurrence cost stays an explicit unpaid dependency until independently proved'},
            'tradeoff': 'quadratic small-index arithmetic becomes a linear interval operator querying up toD; this is not a reduction of required arithmetic information',
            'automatic_steps': ['quotient-block source rewrite', 'signed interval coalescing', 'exact actual evaluations', 'generation of every tail bound', 'independent original-source inverse replay'],
            'supplied_theorem_rules': ['complete Mobius convolution', 'indicator inverse', 'absolute tail telescoping and harmonic estimate'],
            'infinite_smooth_extension': 'review-only; ordinary eta1 floor convergence fails in general, distinct arithmetic-paired admission possible; not used by this experiment',
            'observed_cases': len(results), 'uniform_full_variation_bound_proved': False,
            'uniform_core_bound_proved': False, 'RH_proved': False, 'research_goal_complete': False}


def main():
    if OUT.exists():
        raise FileExistsError('preserve every066 attempt')
    started = time.monotonic()
    counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    receipts = [json.loads(data) for name, data in frozen.items() if name.endswith('_development.json')]
    development = sum(check_receipt(r) for r in receipts)
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in frozen.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    results = []
    try:
        write(OUT/'spec.json', {'spec': SPEC, 'prior_frozen_counts': counts, 'new_frozen_files': len(FILES),
                              'frozen_before_new_sparse_source_or_tail_scores': True})
        names = sorted(p.name for p in RAW.OUT.glob('repair_*.json'))
        if len(names) != 36:
            raise ValueError('all36 old raw repair cases')
        emit('sparse_prefix_started', cases=len(names), workers=SPEC['workers'])
        with mp.get_context('fork').Pool(SPEC['workers']) as pool:
            for result in pool.imap_unordered(evaluate_task, names, chunksize=1):
                write(OUT/result['source_raw_file'].replace('repair_', 'sparse_', 1), result)
                results.append(result)
                emit('sparse_prefix_checked', N=result['N'], y=result['y'], H=result['H'], completed=len(results), total=len(names))
        results.sort(key=lambda r: (r['N'], r['y'], Q(r['theta'])))
        write(OUT/'summary.json', {'rows': [{k: r[k] for k in ('N', 'y', 'H', 'theta', 'old_query_radius', 'new_arithmetic_radius', 'selected_tails', 'block_moments')} |
                                         {'dictionary_shapes': [{'floor_atoms': len(e['floors']), 'step_atoms': len(e['steps']), 'M1': e['step_first_moment']} for e in r['certificate']['endpoints']]}
                                         for r in results], 'uniform_full_bound_proved': False})
        write(OUT/'mechanism_feedback.json', feedback(results))
        for name, data in frozen.items():
            if (ROOT/name).read_bytes() != data:
                raise ValueError('preserve frozen066 '+name)
        parent_peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak = max(r['worker_peak_rss_kib'] for r in results)
        peak_sum = 1024*(parent_peak+SPEC['workers']*worker_peak)
        if peak_sum > SPEC['maximum_aggregate_bytes']:
            raise MemoryError('conservative aggregate process peaks')
        report = {'status': 'ACTUAL_MOBIUS_SPARSE_CONTRACTION_AND_UNIFORM_TAIL_BOUND_HEAD_OPEN',
                  'cases': len(results), 'independent_sparse_certificates': len(results),
                  'exact_raw_coefficients_compared': 2*sum(r['H'] for r in results),
                  'exact_tail_inequalities_verified': 2*sum(r['H'] for r in results),
                  'all_match_saved063_raw_repairs': True, 'core_fill_not_substituted': True,
                  'new_synthetic_tests': sum(r['unique_new_synthetic_tests'] for r in receipts),
                  'test_invocations': sum(sum(t['tests'] for t in r['runs']) for r in receipts),
                  'development_operations': development,
                  'producer_operations': sum(r['producer_operations'] for r in results),
                  'independent_checker_operations': sum(r['checker_operations'] for r in results),
                  'elapsed_seconds': time.monotonic()-started,
                  'parent_peak_rss_kib': parent_peak, 'largest_worker_peak_rss_kib': worker_peak,
                  'conservative_sum_of_process_peaks_bytes': peak_sum,
                  'largest_prospective_algorithm_bytes': max(r['prospective_algorithm_bytes'] for r in results),
                  'workers': SPEC['workers'], 'native_threads_per_worker': 1,
                  'prior_frozen_counts': counts, 'new_frozen_source_count': len(FILES),
                  'uniform_raw_tail_rule_proved': True, 'new_actual_mu_evaluation_through_D': True,
                  'new_masked_signed_source_prefix_values_or_integrals_evaluated': False,
                  'new_unmasked_source_inverse_replay_evaluated': True,
                  'old_scientific_studies_or_suites_replayed': False, 'hashes_used': False,
                  'uniform_full_variation_bound_proved': False, 'uniform_core_bound_proved': False,
                  'RH_proved': False, 'RH_refuted': False}
        write(OUT/'report.json', report)
        emit('sparse_prefix_complete', status=report['status'], elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', {'type': type(exc).__name__, 'message': str(exc), 'completed_cases': len(results), 'RH_proved': False})
        raise


if __name__ == '__main__':
    main()
