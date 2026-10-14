"""Freeze new correlation controls, then independently audit all066 heads."""
import os
for _thread_variable in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[_thread_variable] = '1'

from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import mobius_signed_lag_067 as SEARCH
import check_mobius_signed_lag_067 as CHECK
import run_mobius_sparse_prefix_066 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT/'signed_lag_followup_001'
FILES = ['mobius_signed_lag_067.py', 'test_mobius_signed_lag_067.py',
    'mobius_signed_lag_search_067_development.json', 'check_mobius_signed_lag_067.py',
    'test_check_mobius_signed_lag_067.py', 'mobius_signed_lag_checker_067_development.json',
    'MOBIUS_SIGNED_LAG_CHECK_SCOPE_067.txt', 'SPARSE_HEAD_MECHANISM_REVIEW_067.txt',
    'run_mobius_signed_lag_067.py', 'mobius_signed_lag_protocol_067.txt']
SPEC = {'cases': 'all36 completed066 sources, SAME raw head at both endpoints',
    'head_stop': 'ceil(H/2)-1', 'blocks': '[2^k,min(2^(k+1)-1,head_stop)]',
    'exponents': SEARCH.DEFAULT_EXPONENTS, 'extra_no_near_lag_baseline': True,
    'candidate_enumeration': 'all reduced a/b in[0,1],b<=7, plus1/(2^k+1),k0..8',
    'ranking': 'Pareto paid exponent and observed unpaid risk; retain every candidate',
    'new_signed_correlation_values': True, 'fresh_final_holdout': False,
    'adaptive_fitting': False, 'anticipated_winner': None,
    'workers': 3, 'native_threads_per_worker': 1, 'maximum_aggregate_bytes': 16*1024**3,
    'work_cap_per_case_meter': 300_000_000_000, 'module_seconds': 7200,
    'uniform_full_head_bound_claim': False, 'hashes_used': False}


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve066 '+name)
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['independent_sparse_certificates'] != 36 or not report['uniform_raw_tail_rule_proved'] or report['RH_proved']:
        raise ValueError('completed066 and open full bound')
    return counts+[len(PRIOR.FILES)]


def bind_sparse(saved):
    source, verdict = saved['certificate'], saved['verification']
    if not verdict['verified'] or not verdict['raw_short_only'] or not saved['raw_coefficients_match_at_every_row']:
        raise ValueError('same verified raw sparse source')
    if not saved['comparison_is_raw_only'] or not saved['same_saved_raw_source_admission_reused']:
        raise ValueError('raw branch source scope')
    for key in ('N', 'y', 'H'):
        if saved[key] != source[key] or verdict[key] != source[key]:
            raise ValueError('same source parameters')
    if saved['parameters'] != source['parameters'] or verdict['parameters'] != source['parameters']:
        raise ValueError('same registered arithmetic source')
    if saved['RH_proved'] or saved['uniform_full_variation_bound_proved']:
        raise ValueError('preserve unclosed full arithmetic bound')
    return source


def evaluate_task(name):
    started = time.monotonic()
    saved = json.loads((PRIOR.OUT/name).read_text())
    source = bind_sparse(saved)
    meter = SEARCH.Meter(cap=SPEC['work_cap_per_case_meter'], seconds=SPEC['module_seconds'])
    cm = CHECK.Meter(cap=SPEC['work_cap_per_case_meter'], seconds=SPEC['module_seconds'])
    cert = SEARCH.construct(source, SPEC['exponents'], meter)
    verdict = CHECK.verify_lag(cert, cm)
    if not verdict['verified']:
        raise ValueError('independently verified complete lag moments')
    summary = SEARCH.summarize(cert)
    for endpoint, compiled in zip(source['endpoints'], cert['endpoints']):
        actual = sum((abs(Q(row['coefficient'])) for row in endpoint['rows'][:cert['head_stop']]), Q(0))
        if actual != sum((Q(b['actual_head_variation']) for b in compiled['blocks']), Q(0)):
            raise ValueError('complete same066 head coefficients')
    return {'source_sparse_file': name, 'N': source['N'], 'y': source['y'], 'H': source['H'],
        'theta': saved['theta'], 'certificate': cert, 'verification': verdict,
        'reused066_source_verification': saved['verification'], 'summary': summary,
        'same_raw_source_head': True, 'all_lags_and_rows_verified': True,
        'producer_operations': meter.operations, 'checker_operations': cm.operations,
        'prospective_algorithm_bytes': meter.peak_bytes_estimate,
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'elapsed_seconds': time.monotonic()-started,
        'uniform_far_correlation_bound_proved': False, 'RH_proved': False}


def feedback(results):
    return {'schema': 'mobius-signed-lag-bound-feedback-v1',
        'previous_goal_turn': '066 substantive: actual-Mobius contraction and uniform raw terminal bound',
        'current_goal_turn': '067 exact signed lag compiler, uniform diagonal/near-lag payment, and scoped barrier review',
        'source_scope': 'same RAW source and full original prefix/RH objective; core_inverse not substituted',
        'uniform_paid_rule': {
            'g': 'f_y-f_full=-1[d>y]*(W_p(d)-r*W_q(d)); |g|<=2',
            'kappa': 'g(jn)-g((j+1)n), hence |kappa|<=4',
            'moment': 'E_I=D_I+2*sum_(h>0) R_I(h)',
            'R': 'sum_(j in I,n>=1) mu(n)mu(n+h)kappa_j(n)kappa_j(n+h)',
            'diagonal': 'D_I<=4M1/L', 'per_lag': '|R_I(h)|<=4M1/L',
            'short_lag_paid': 'E_I<=(4+8B)M1/L + (2*sum_(h>B)R_I(h))_+',
            'M1': 'sum|a_T|T=O(Nlog(2N)) uniformly y, already proved066',
            'baseline_head': 'F_head+2*(number of dyadic head blocks)*sqrt(M1)+Risk',
            'power_lag_head': 'B<=N^delta gives paid O(N^((1+delta)/2)*log(2N)^(3/2))',
            'all_rational_exponents': 'all rationaldelta in[0,1] mathematically; finite implementation capacity explicit'},
        'next_obligation': {
            'priority': 'uniform actual signed FAR correlation control',
            'baseline': 'sum_I sqrt(|I|*(2*sum_(h>0)R_I(h))_+) = Oeps(N^(1/2+eps))',
            'fractional_alternative': 'for everydelta in a cofinal sequence delta->0 and everyeta>0, B=floorN^delta and sum_I sqrt(|I|*(2*sum_(h>B)R_I(h))_+) = O_(delta,eta)(N^((1+delta)/2+eta))',
            'uniformity': 'every required N and prefixy, H=floor√N, both ratioendpoints, each positiveepsilon; constants independentN,y',
            'sufficient_not_necessary': True,
            'signed_joining_required': 'same ordinarymu in all rows, channels and lags; do not replace joined far sum by assumed absolute-Chowla bounds',
            'no_new_arithmetic_radius': True,
            'not_dischargeable_by': ['finite exact energy evaluation', 'assumed RH Mertens control',
                'a fixed positive delta without a cofinal transfer', 'unpaid recurrence or a target encoded as an auxiliary constant']},
        'reviewed_excluded_grammars': [
            {'family': 'divisor annihilator supported below16k followed by residual triangle',
             'source': 'N15k,y16k,r eitherendpoint,k large',
             'price_lower': 'k-floor(sqrt20k)', 'scope': 'not a signed-head lower bound'},
            {'family': 'fixed finite prime pairing then rough squarefree absolute price',
             'source': 'same actual joined source', 'price_lower': 'Omega_P(k)',
             'scope': 'fixedP only; does not exclude growingP or signed correlation controls'}],
        'review_only_additional_paid_regions': 'zero/full-floor closures pay y orD-y <=√N polylogN; not implemented as new scientific candidates',
        'automatic_actions': ['compile all exact lag kernels', 'generate rational lag cutoffs',
            'prove finite diagonal/near/far bounds', 'retain every remaining correlation lemma',
            'rank finite evidence across paid powers and observed risks', 'independent original-source integer correlation replay'],
        'supplied_rules': ['bounded W profile', 'moment expansion', 'triangle for near lags', 'Cauchy/dyadic transfer', 'endpoint convexity of actual norm'],
        'observed_cases': len(results), 'uniform_far_correlation_bound_proved': False,
        'uniform_full_head_bound_proved': False, 'uniform_core_bound_proved': False,
        'RH_proved': False, 'research_goal_complete': False}


def main():
    if OUT.exists():
        raise FileExistsError('preserve every067 attempt')
    started = time.monotonic()
    counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    receipts = [json.loads(data) for name, data in frozen.items() if name.endswith('_development.json')]
    development = sum(check_receipt(r) for r in receipts)
    if any(r['final_status'] != 'PASS' for r in receipts):
        raise ValueError('new development gates passed')
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in frozen.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    results = []
    try:
        write(OUT/'spec.json', {'spec': SPEC, 'prior_frozen_counts': counts,
            'new_frozen_files': len(FILES), 'frozen_before_new_scientific_correlations': True})
        names = sorted(p.name for p in PRIOR.OUT.glob('sparse_*.json'))
        if len(names) != 36:
            raise ValueError('all36 completed066 sources')
        emit('signed_lag_started', cases=len(names), workers=SPEC['workers'], exponents=len(SPEC['exponents']))
        with mp.get_context('fork').Pool(SPEC['workers']) as pool:
            for result in pool.imap_unordered(evaluate_task, names, chunksize=1):
                write(OUT/result['source_sparse_file'].replace('sparse_', 'lag_', 1), result)
                results.append(result)
                emit('signed_lag_checked', N=result['N'], y=result['y'], H=result['H'], completed=len(results), total=len(names))
        results.sort(key=lambda r: (r['N'], r['y'], Q(r['theta'])))
        write(OUT/'summary.json', {'rows': [{k: r[k] for k in ('N', 'y', 'H', 'theta', 'summary')} for r in results],
            'uniform_full_head_bound_proved': False})
        write(OUT/'mechanism_feedback.json', feedback(results))
        for name, data in frozen.items():
            if (ROOT/name).read_bytes() != data:
                raise ValueError('preserve frozen067 '+name)
        parent_peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak = max(r['worker_peak_rss_kib'] for r in results)
        peak_sum = 1024*(parent_peak+SPEC['workers']*worker_peak)
        if peak_sum > SPEC['maximum_aggregate_bytes']:
            raise MemoryError('conservative aggregate process peaks')
        blocks = [b for r in results for e in r['certificate']['endpoints'] for b in e['blocks']]
        report = {'status': 'UNIFORM_DIAGONAL_AND_SHORT_LAGS_PAID_SIGNED_FAR_CONTROL_OPEN',
            'cases': len(results), 'independent_lag_certificates': len(results),
            'dyadic_endpoint_blocks': len(blocks),
            'exact_head_rows_verified': sum(len(b['row_sums_scaled']) for b in blocks),
            'exact_lag_coefficients_verified': sum(len(b['correlation_numerators']) for b in blocks),
            'fractional_lag_certificates': sum(len(b['candidates']) for b in blocks),
            'diagonal_only_counterexamples': sum(Q(b['signed_cross']) > 0 for b in blocks),
            'negative_signed_cross_blocks': sum(Q(b['signed_cross']) < 0 for b in blocks),
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
            'uniform_diagonal_bound_proved': True, 'uniform_short_lag_bound_proved': True,
            'same_raw_branch_source': True, 'old_scientific_studies_or_suites_replayed': False,
            'hashes_used': False, 'fresh_holdout_claim': False,
            'uniform_far_correlation_bound_proved': False, 'uniform_full_head_bound_proved': False,
            'uniform_core_bound_proved': False, 'RH_proved': False, 'RH_refuted': False}
        write(OUT/'report.json', report)
        emit('signed_lag_complete', status=report['status'], elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', {'type': type(exc).__name__, 'message': str(exc),
            'completed_cases': len(results), 'RH_proved': False})
        raise


if __name__ == '__main__':
    main()
