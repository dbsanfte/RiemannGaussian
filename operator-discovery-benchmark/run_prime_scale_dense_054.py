"""Dense new-scale audit of the fixed053 signed arithmetic inequalities."""
from collections import Counter
from pathlib import Path
import json
import multiprocessing as mp
import resource
import time
import numpy as np

import run_prime_scale_search_053 as PRIOR

ROOT = Path(__file__).resolve().parent
PARENT = PRIOR.OUT
OUT = PARENT/'dense_followup_001'
SKIP = sorted(set(PRIOR.TRAIN+PRIOR.FINAL))
MAX_N = 128000
FILES = ['prime_scale_dense_054.py', 'test_prime_scale_dense_054.py',
    'prime_scale_dense_054_development.json', 'check_prime_scale_dense_054.py',
    'test_check_prime_scale_dense_054.py', 'check_prime_scale_dense_054_development.json',
    'PRIME_SCALE_DENSE_CHECK_SCOPE_054.txt',
    'PRIME_SCALE_CANDIDATE_REVIEW_054.txt', 'run_prime_scale_dense_054.py',
    'test_prime_scale_dense_runner_054.py', 'prime_scale_dense_runner_054_development.json',
    'prime_scale_dense_protocol_054.txt']
write, emit = PRIOR.write, PRIOR.emit


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PARENT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in snapshots):
        raise ValueError('preserve all frozen053 sources')
    report = json.loads((PARENT/'report.json').read_text())
    if report['RH_proved'] is not False or report['uniform_arithmetic_bound_proved'] is not False:
        raise ValueError('preserve OPEN signed arithmetic premise')
    return counts+[len(snapshots)]


def expected_coverage(request, stop_at=None):
    """Independently derive the new finite domain, including early stopping."""
    maximum = MAX_N//request['q']**(len(request['coefficients'])-1)
    if stop_at is not None and (type(stop_at) is not int or not 2 <= stop_at <= maximum or stop_at in SKIP):
        raise ValueError('first witness must belong to new integer domain')
    end = maximum if stop_at is None else stop_at
    skipped = sum(2 <= n <= maximum for n in SKIP)
    tested = end-1-sum(2 <= n <= end for n in SKIP)
    total_new = maximum-1-skipped
    return {'minimum': 2, 'maximum': maximum, 'skipped_prior': skipped,
        'new_available': total_new, 'tested': tested,
        'untested_after_stop': total_new-tested, 'stop_at': stop_at}


def admit_scope(request, producer_counts, witness=None, independent=None):
    """Require complete declared coverage and independent strict refutation."""
    stop_at = None if witness is None else witness['N']
    scope = expected_coverage(request, stop_at)
    if producer_counts != {k: scope[k] for k in ('tested', 'skipped_prior', 'untested_after_stop')}:
        raise ValueError('dense coverage disagrees with complete fresh integer domain')
    if witness is None:
        if independent is not None:
            raise ValueError('no witness verification without a witness')
        status = 'OPEN_AFTER_DENSE_FINITE_TESTS'
    else:
        if independent is None or independent.get('verified') is not True or independent.get('status') != 'FINITE_REFUTATION':
            raise ValueError('independent strict witness verification required')
        if independent.get('request') != request or independent.get('N') != stop_at:
            raise ValueError('independent verification must concern the same fixed bound and scale')
        status = 'REFUTED_FIXED_UNIFORM_BOUND'
    return {'status': status, 'coverage': scope, 'uniform_arithmetic_bound_proved': False,
        'RH_proved': False, 'RH_refuted': False}


def load_fields(alpha):
    stem = 'source_'+alpha.replace('/', '_')+'_training'
    receipt = json.loads((PARENT/(stem+'.json')).read_text())
    source = receipt['source']
    if (receipt['alpha'] != alpha or source['alpha'] != alpha or source['max_n'] != MAX_N
            or source['dyadic_bits'] != 32 or receipt['independent_verification']['all_indices_checked'] is not True):
        raise ValueError('declared previously checked053 source archive required')
    with np.load(PARENT/(stem+'.npz'), allow_pickle=False) as stored:
        if set(stored.files) != {'mu', 'prefix_w', 'prefix_up', 'prefix_down'}:
            raise ValueError('exact saved array archive fields')
        arrays = {name: stored[name] for name in stored.files}
    return {'alpha': alpha, 'max_n': MAX_N, 'bits': 32, 'metadata': source, **arrays}


def audit_alpha(task):
    import prime_scale_dense_054 as DENSE
    import check_prime_scale_dense_054 as CHECK
    alpha, selected = task['alpha'], task['selected']
    pm = DENSE.Meter(cap=20_000_000_000, seconds=7200)
    cm = CHECK.Meter(cap=200_000_000_000, seconds=7200)
    dense = DENSE.dense_source(load_fields(alpha), pm)
    context = None
    rows = []
    for entry in selected:
        result = DENSE.first_counterexample(entry, dense, SKIP, pm)
        witness = result['first_counterexample']
        independent = None
        if witness is not None:
            if context is None:
                context = CHECK.prepare_context(cm)
            independent = CHECK.verify_witness(entry['request'], witness, cm, context)
        scope = admit_scope(entry['request'], {
            'tested': result['new_scales_tested'],
            'skipped_prior': result['skipped_preobserved_count'],
            'untested_after_stop': result['untested_after_counterexample']}, witness, independent)
        if (result['id'] != entry['id'] or result['request'] != entry['request']
                or result['minimum'] != scope['coverage']['minimum']
                or result['maximum'] != scope['coverage']['maximum']
                or result['skip_scales_in_domain'] != [n for n in SKIP if n <= scope['coverage']['maximum']]
                or result['new_scales_total'] != scope['coverage']['new_available']
                or result['finite_pass_count']+result['unresolved_count']+int(witness is not None) != scope['coverage']['tested']):
            raise ValueError('complete producer coverage and status accounting required')
        rows.append({'id': entry['id'], 'request': entry['request'], 'producer': result,
            'independent_witness_verification': independent, **scope})
    return {'alpha': alpha, 'dense': dense, 'rows': rows,
        'producer_counts': pm.counts(), 'checker_operations': cm.operations,
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}


def summarize(rows):
    return [{k: row[k] for k in ('id', 'request', 'status', 'coverage',
        'uniform_arithmetic_bound_proved', 'RH_proved', 'RH_refuted')} | {
            'finite_pass_count': row['producer']['finite_pass_count'],
            'unresolved_count': row['producer']['unresolved_count'],
            'first_counterexample_N': None if row['producer']['first_counterexample'] is None
                else row['producer']['first_counterexample']['N']}
        for row in rows]


def main():
    started = time.monotonic()
    if OUT.exists():
        raise FileExistsError('preserve completed or failed054 application')
    counts = validate_parent()
    development_operations = sum(PRIOR.PRIOR.check_receipt(json.loads((ROOT/name).read_text()))
        for name in FILES if name.endswith('_development.json'))
    selected = [{k: row[k] for k in ('id', 'request')}
        for row in json.loads((PARENT/'selected.json').read_text())['selected']]
    if len(selected) != 6 or len({r['id'] for r in selected}) != 6:
        raise ValueError('preserve six distinct053 requests')
    if any(r['request']['bound'] != {'C': '2', 'log_power': '0', 'minimum': 2,
            'normalization': 'divide_by_alpha'} for r in selected):
        raise ValueError('fixed C2 eta0 bounds required')
    snapshots = {name: (ROOT/name).read_bytes() for name in FILES}
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, data in snapshots.items():
        (OUT/'source_snapshot'/name).write_bytes(data)
    try:
        write(OUT/'protocol.json', {'selected': selected, 'source_maximum': MAX_N,
            'skip_scales': SKIP, 'bounds_refitted': False,
            'domains': [{'id': r['id'], **expected_coverage(r['request'])} for r in selected],
            'stop_rule': 'per request ascending newN; first strict refutation stops that request',
            'producer': 'reuse053 atoms; exact integer stride convolution and signed interval combinations',
            'witness_checker': 'new source-specific Mobius and transcendental reconstruction; complete divisor-floor prefixes and signed combination',
            'comparisons': 'exact integer squares for C2 eta0',
            'source_array_reuse': 'five checked053 archives; dense A arrays saved for future reuse',
            'reconstruction_overlap': 'any new witness reconstruction overlaps053 atoms, with counts reported',
            'workers': 3, 'aggregate_memory_limit_bytes': 16*1024**3,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'hashes_used': False, 'old_scientific_studies_replayed': False})
        emit('dense_protocol_frozen', requests=len(selected), source_maximum=MAX_N,
            fresh_word_scale_pairs=sum(expected_coverage(r['request'])['new_available'] for r in selected))
        tasks = [{'alpha': alpha, 'selected': [r for r in selected if r['request']['alpha'] == alpha]}
            for alpha in sorted({r['request']['alpha'] for r in selected})]
        rows, source_receipts = [], []
        with mp.get_context('fork').Pool(3) as pool:
            for result in pool.imap_unordered(audit_alpha, tasks):
                dense = result.pop('dense')
                stem = 'dense_'+result['alpha'].replace('/', '_')
                with (OUT/(stem+'.npz')).open('xb') as f:
                    np.savez(f, Acenter=dense.Acenter, Adown=dense.Adown, Aup=dense.Aup)
                receipt = {k: v for k, v in result.items() if k != 'rows'}
                receipt['dense_source'] = dense.metadata()
                receipt['array_file'] = stem+'.npz'
                write(OUT/(stem+'.json'), receipt)
                source_receipts.append(receipt)
                rows.extend(result['rows'])
                write(OUT/(stem+'_audit.json'), {'rows': result['rows']})
                emit('dense_alpha_audited', alpha=result['alpha'],
                    tested=sum(r['coverage']['tested'] for r in result['rows']),
                    statuses=[r['status'] for r in result['rows']])
        order = {entry['id']: i for i, entry in enumerate(selected)}
        rows.sort(key=lambda row: order[row['id']])
        if [row['id'] for row in rows] != [entry['id'] for entry in selected]:
            raise ValueError('each selected053 request audited exactly once')
        assessment = summarize(rows)
        write(OUT/'assessment.json', {'rows': assessment, 'uniform_arithmetic_bound_proved': False,
            'RH_proved': False, 'RH_refuted': False})
        write(OUT/'next_search_input.json', {'schema': 'prime-scale-dense-feedback-v1',
            'parent': str((PARENT/'next_search_input.json').relative_to(ROOT)),
            'targets': assessment,
            'fixed_bound_status': 'only independent counterexamples refute; all other uniform premises remain OPEN',
            'analytical_attempt': 'PRIME_SCALE_CANDIDATE_REVIEW_054.txt',
            'paid_generic_reductions': ['base-q digit compilation',
                'prime insertion and positive shifted-log defect with unit exception',
                'exact child/parent/p-free block decomposition',
                'all-integer recovery between linear and quadratic scale filters at the SAME alpha'],
            'joint_frontier': {
                'domain': 'fixed0<alpha<1, primep, integerN>=2',
                'K': '-sum_(d|n)mu(d)*(logd)^alpha',
                'B_p': 'sum_(N<m<=pN)K(m)',
                'J_p': 'sum_(pN<n<=p^2N,p not dividing n)K(n)',
                'D_p': 'sum_(N<m<=pN,p not dividing m)[K(m)-K(pm)] >=0',
                'exact_source': 'J_p-(p-1)*B_p-D_p = A(p^2N)-(p+1)A(pN)+pA(N)',
                'target': '|exact_source| <=C*alpha*sqrt(N), uniformlyN>=2',
                'unpaid_leaf': 'control the joint fresh/parent/prime-defect arithmetic correlation'},
            'next_search_priority': 'discover an auxiliary or pairing controlling the joint source; no constant refit or equivalent restatement counts as scale gain',
            'uniform_arithmetic_bound_proved': False, 'RH_proved': False})
        validate_parent()
        if any((ROOT/name).read_bytes() != data for name, data in snapshots.items()):
            raise ValueError('frozen054 sources changed during application')
        report = {'status': 'DENSE_SIGNED_BOUND_AUDIT_COMPLETE_UNIFORM_PROOF_OPEN',
            'selected': assessment, 'selected_count': len(rows),
            'candidate_status_counts': dict(Counter(r['status'] for r in rows)),
            'new_word_scale_pairs_tested': sum(r['coverage']['tested'] for r in rows),
            'finite_pass_count': sum(r['producer']['finite_pass_count'] for r in rows),
            'unresolved_count': sum(r['producer']['unresolved_count'] for r in rows),
            'independently_verified_counterexamples': sum(r['producer']['first_counterexample'] is not None for r in rows),
            'untested_after_stop': sum(r['coverage']['untested_after_stop'] for r in rows),
            'producer_operations': sum(r['producer_counts']['operations'] for r in source_receipts),
            'new_witness_checker_operations': sum(r['checker_operations'] for r in source_receipts),
            'new_producer_atoms_evaluated': 0,
            'development_operations': development_operations,
            'persistent_dense_array_bytes': sum(r['dense_source']['persistent_array_bytes'] for r in source_receipts),
            'parent_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_individual_worker_peak_rss_kib': max(r['worker_peak_rss_kib'] for r in source_receipts),
            'workers': 3, 'aggregate_memory_limit_bytes': 16*1024**3,
            'elapsed_seconds': time.monotonic()-started,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'bounds_refitted': False, 'hashes_used': False,
            'uniform_arithmetic_bound_proved': False, 'RH_proved': False, 'RH_refuted': False,
            'old_scientific_studies_replayed': False}
        write(OUT/'report.json', report)
        emit('dense_audit_completed', statuses=report['candidate_status_counts'],
            tested=report['new_word_scale_pairs_tested'], elapsed_seconds=report['elapsed_seconds'])
    except Exception as error:
        write(OUT/'failure.json', {'type': type(error).__name__, 'message': str(error),
            'elapsed_seconds': time.monotonic()-started})
        raise


if __name__ == '__main__': main()
