"""Frozen paired-lemma search with independent source and program admission."""
import os
for _key in ('OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'OMP_NUM_THREADS'):
    os.environ[_key] = '1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
import resource
import time

import mobius_prime_moment_075 as SEARCH
import check_mobius_prime_moment_075 as CHECK
import run_mobius_centered_storage_074 as PRIOR
from run_fractional_prime_kernel_051 import write, emit

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT / 'prime_moment_followup_001'
FILES = ['mobius_prime_moment_075.py', 'test_mobius_prime_moment_075.py',
         'test_mobius_prime_moment_integration_075.py', 'mobius_prime_moment_search_075_development.json',
         'check_mobius_prime_moment_075.py', 'test_check_mobius_prime_moment_075.py',
         'mobius_prime_moment_checker_075_development.json', 'MOBIUS_PRIME_MOMENT_CHECK_SCOPE_075.txt',
         'MOBIUS_PRIME_MOMENT_REVIEW_075.txt', 'mobius_prime_moment_protocol_075.txt',
         'run_mobius_prime_moment_075.py']
SPEC = dict(source=SEARCH.SOURCE_SPEC, q=['1', '33/32', '129/128'], base_u=4096, precision=20,
            discovery_k_anchors=[64, 96, 128, 192, 256, 384, 512],
            adaptation_k_anchors=[768, 1024, 1536, 2048, 3072, 3723, 4096, 6144,
                                  8192, 12288, 16384, 21142, 24576, 32768],
            final_k_anchors=[40960, 49152, 65536],
            phases=list(range(80)), anchor_rule='u=80*k-phase, every phase0..79',
            workers=3, native_threads_per_worker=1, maximum_aggregate_bytes=16*1024**3,
            module_seconds=7200, work_limit=300_000_000_000,
            selected_per_class=['best_conditional_transfer_price', 'best_innovation_constant'],
            known_direct_cauchy_recovery_slot=True, zero_operator_baseline=True,
            formulas_selected_using_discovery_only=True, adaptive_refits=0,
            new_final_only_after_both_known_lemmas_pass=True,
            known_arithmetic_prefix_through=655360, largest_final_prefix=1310720,
            complete_base_checked=True, sparse_parent_sampling=True,
            hashes_used=False, uniform_source_bound_proved=False, RH_proved=False)


def scales(anchors):
    return sorted({80*k-phase for k in anchors for phase in SPEC['phases']})


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve074 pre-run source ' + name)
    publication = json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve074 exact feedback ' + name)
    if publication['overall_candidate_refutations'] != 4 or publication['RH_proved']:
        raise ValueError('preserve074 candidate disposition')
    return counts + [len(PRIOR.FILES), len(publication['postrun_files'])]


def require_admitted_source(data, admission):
    """Source proof is a separate mandatory dependency, before any finite claim."""
    if admission['source_admission']['status'] != 'VERIFIED':
        raise ValueError('independent arithmetic source admission required')
    if admission['source_spec'] != data['spec'] or admission['scales'] != [r['u'] for r in data['rows']]:
        raise ValueError('source admission artifact binding')
    if not data['rows']:
        raise ValueError('nonempty scientific source')


def source_phase(name, parents):
    start = time.monotonic()
    pm, cm = SEARCH.Meter(SPEC['work_limit']), CHECK.Meter(SPEC['work_limit'])
    data = SEARCH.make_data(SPEC['source'], parents, pm)
    admitted = CHECK.verify_data(data, cm)
    result = dict(source_admission=admitted, source_spec=data['spec'], scales=parents,
                  rows=len(parents), producer_operations=pm.ops, checker_operations=cm.ops,
                  prospective_bytes=max(pm.peak_bytes, cm.peak_bytes),
                  elapsed_seconds=time.monotonic()-start)
    require_admitted_source(data, result)
    write(OUT/(name+'_data.json'), data)
    write(OUT/(name+'_source_admission.json'), result)
    emit('prime_moment_source_admitted', phase=name, rows=len(parents), elapsed_seconds=result['elapsed_seconds'])
    return data, result


_DISCOVERY = _ADAPTATION = _LEARNING = None


def initialize_worker():
    global _DISCOVERY, _ADAPTATION, _LEARNING
    _LEARNING = json.loads((OUT/'learning_data.json').read_text())
    admission = json.loads((OUT/'learning_source_admission.json').read_text())
    require_admitted_source(_LEARNING, admission)
    discovery_scales = set(scales(SPEC['discovery_k_anchors']))
    _DISCOVERY = dict(_LEARNING, rows=[r for r in _LEARNING['rows'] if r['u'] in discovery_scales])
    _ADAPTATION = dict(_LEARNING, rows=[r for r in _LEARNING['rows'] if r['u'] not in discovery_scales])


def moment_task(task):
    start = time.monotonic()
    pm, cm = SEARCH.Meter(SPEC['work_limit']), CHECK.Meter(SPEC['work_limit'])
    shape = list(map(Q, task['shape']))
    prices = SEARCH.price_bounds(SPEC['source'], SPEC['base_u'])
    if task['mode'] == 'universal_direct_cauchy':
        beta, fit = SEARCH.cauchy_beta(shape), dict(rule='weighted Cauchy, sum a_i^2/beta_i=1')
    else:
        beta, fit = SEARCH.fit_beta(shape, _DISCOVERY['rows'], prices, pm)
    assessment = SEARCH.correlation_assessment(shape, beta, _ADAPTATION['rows'], pm)
    witness_admission = None
    if assessment['failures']:
        # An independently checked homogeneous witness suffices to reject
        # every nonzero amplitude of this exact shape/beta pair.
        u = assessment['worst']['u']
        row = next(r for r in _ADAPTATION['rows'] if r['u'] == u)
        amplitude = SEARCH.amplitudes(SEARCH.dot(beta, prices))[0]
        program = SEARCH.make_program(SPEC['source'], [amplitude*a for a in shape],
                    [amplitude*amplitude*b for b in beta], '1', [row], SPEC['base_u'], SPEC['precision'], pm)
        one = dict(_ADAPTATION, rows=[row])
        checked = CHECK.verify_program(program, one, cm, scales=[u])
        if checked['status'] != 'REFUTED' or not any(w['lemma'] == 'correlation' for w in checked['failures']):
            raise ArithmeticError('independent homogeneous correlation witness')
        witness_admission = dict(program=program, evaluation=checked,
                                 source_dependency='learning_source_admission.json; exact selected row',
                                 all_nonzero_amplitudes_fail_same_correlation=True)
    result = dict(task, beta=list(map(str, beta)), price=str(SEARCH.dot(beta, prices)),
                  fit=fit, adaptation_correlation=assessment, independent_witness=witness_admission,
                  producer_operations=pm.ops, checker_operations=cm.ops,
                  prospective_bytes=max(pm.peak_bytes, cm.peak_bytes),
                  elapsed_seconds=time.monotonic()-start,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  uniform_source_bound_proved=False, RH_proved=False)
    write(OUT/('moment_'+task['id']+'.json'), result)
    return result


def candidate_task(q):
    start = time.monotonic()
    pm, cm = SEARCH.Meter(SPEC['work_limit']), CHECK.Meter(SPEC['work_limit'])
    records = json.loads((OUT/'moment_summary.json').read_text())['records']
    result = SEARCH.propose_programs(records, _DISCOVERY, q, SPEC['base_u'], SPEC['precision'], pm)
    result['programs'].append(dict(program=result.pop('baseline'), selection=dict(kind='baseline', selected_by=['zero_operator_control']),
                                   parent_record=None, correlation_mode='trivial', origins=['baseline']))
    eligible = []
    for index, item in enumerate(result['programs']):
        item['id'] = 'q'+q.replace('/', '_')+'_p'+str(index)
        admission = CHECK.verify_program(item['program'], _LEARNING, cm)
        if admission['status'] != 'VERIFIED_ON_FINITE_DOMAIN' or not admission['conditional_induction_verified']:
            raise ValueError('discovery program admission '+str(admission))
        adaptation = CHECK.verify_program(item['program'], _LEARNING, cm,
                                          scales=[r['u'] for r in _ADAPTATION['rows']])
        if adaptation['status'] == 'INVALID':
            raise ValueError('invalid adaptation program '+str(adaptation))
        item.update(discovery_admission=admission, adaptation=adaptation,
                    source_dependency='learning_source_admission.json',
                    final_eligible=adaptation['status']=='VERIFIED_ON_FINITE_DOMAIN',
                    unpaid_leaves=SEARCH.next_obligations(item, adaptation))
        if item['final_eligible']:
            eligible.append(item['id'])
    result.update(eligible_ids=eligible, producer_operations=pm.ops, checker_operations=cm.ops,
                  prospective_bytes=max(pm.peak_bytes, cm.peak_bytes), elapsed_seconds=time.monotonic()-start,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  uniform_source_bound_proved=False, RH_proved=False)
    file = 'candidates_'+q.replace('/', '_')+'.json'
    write(OUT/file, result)
    return dict(q=q, file=file, programs=len(result['programs']), eligible_ids=eligible,
                producer_operations=pm.ops, checker_operations=cm.ops,
                prospective_bytes=result['prospective_bytes'], elapsed_seconds=result['elapsed_seconds'],
                worker_peak_rss_kib=result['worker_peak_rss_kib'])


def final_task(item):
    start = time.monotonic()
    data = json.loads((OUT/'final_data.json').read_text())
    admission = json.loads((OUT/'final_source_admission.json').read_text())
    require_admitted_source(data, admission)
    if not item['final_eligible'] or item['adaptation']['status'] != 'VERIFIED_ON_FINITE_DOMAIN':
        raise ValueError('both known lemmas must pass before new final evaluation')
    cm = CHECK.Meter(SPEC['work_limit'])
    result = CHECK.verify_program(item['program'], data, cm, scales=[r['u'] for r in data['rows']])
    if result['status'] == 'INVALID':
        raise ValueError('invalid frozen final program')
    record = dict(id=item['id'], evaluation=result, unpaid_leaves=SEARCH.next_obligations(item, result),
                  source_dependency='final_source_admission.json', checker_operations=cm.ops,
                  elapsed_seconds=time.monotonic()-start,
                  worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  uniform_source_bound_proved=False, RH_proved=False)
    write(OUT/('final_'+item['id']+'.json'), record)
    return record


def collect(pool, function, tasks, start, event):
    results, peak = [], 0
    iterator = pool.imap_unordered(function, tasks, chunksize=1)
    last_emit = time.monotonic()
    while len(results) < len(tasks):
        if time.monotonic()-start > SPEC['module_seconds']:
            raise TimeoutError('075 whole-stage deadline')
        used = PRIOR.PRIOR.rss([os.getpid()] + [p.pid for p in pool._pool])
        peak = max(peak, used)
        if used > SPEC['maximum_aggregate_bytes']:
            raise MemoryError('075 aggregate memory')
        try:
            item = iterator.next(timeout=1)
        except mp.TimeoutError:
            continue
        results.append(item)
        if len(results) == len(tasks) or time.monotonic()-last_emit > 10:
            emit(event, completed=len(results), total=len(tasks))
            last_emit = time.monotonic()
    return results, peak


def main():
    if OUT.exists():
        raise FileExistsError('preserve every075 attempt')
    start = time.monotonic()
    counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    receipts = [json.loads(content) for name, content in frozen.items() if name.endswith('_development.json')]
    if any(r.get('status', r.get('final_status', r.get('latest_outcome'))) != 'PASS' for r in receipts):
        raise ValueError('development latest outcomes must pass')
    OUT.mkdir()
    (OUT/'source_snapshot').mkdir()
    for name, content in frozen.items():
        with (OUT/'source_snapshot'/name).open('xb') as stream:
            stream.write(content)
    try:
        write(OUT/'spec.json', dict(spec=SPEC, prior_frozen_counts=counts, new_frozen_files=len(FILES)))
        obligations = json.loads((PRIOR.OUT/'signed_prime_dilation_obligations.json').read_text())
        write(OUT/'input_obligations074.json', obligations)
        parents = sorted(set(scales(SPEC['discovery_k_anchors'])+scales(SPEC['adaptation_k_anchors'])))
        data, learning_phase = source_phase('learning', parents)
        learning_bytes = (OUT/'learning_data.json').read_bytes()
        discovery_set = set(scales(SPEC['discovery_k_anchors']))
        discovery = dict(data, rows=[r for r in data['rows'] if r['u'] in discovery_set])
        pm = SEARCH.Meter(SPEC['work_limit'])
        dictionary = SEARCH.catalog(SPEC['source'], obligations)
        proposals = SEARCH.minimax_directions(discovery, SPEC['q'], pm)
        known = {tuple(r['shape']): r for r in dictionary}
        for row in proposals:
            if 'shape' not in row:
                continue
            key = tuple(row['shape'])
            if key in known:
                known[key]['origins'].extend(row['origins'])
            else:
                known[key] = row
                dictionary.append(row)
        tasks = []
        for shape in dictionary:
            for mode in ['learned_diagonal_moment'] + (['universal_direct_cauchy'] if shape['kind']=='direct_only' else []):
                tasks.append(dict(shape, mode=mode, id=str(len(tasks)).zfill(3)))
        write(OUT/'operator_catalog.json', dict(shapes=dictionary, moment_tasks=tasks,
                minimax_proposals=proposals, producer_operations=pm.ops,
                inherited_exact_obligation_changes_actual_grammar=True))
        del data, discovery
        with mp.get_context('spawn').Pool(SPEC['workers'], initializer=initialize_worker) as pool:
            records, peak1 = collect(pool, moment_task, tasks, start, 'prime_moment_controls_searched')
            records.sort(key=lambda r: r['id'])
            write(OUT/'moment_summary.json', dict(records=records,
                numerical_correlation_refutations=sum(bool(r['adaptation_correlation']['failures']) for r in records),
                independent_correlation_witnesses=sum(r['independent_witness'] is not None for r in records),
                uniform_prime_correlation_proved=False, RH_proved=False))
            candidates, peak2 = collect(pool, candidate_task, SPEC['q'], start, 'prime_moment_programs_frozen')
            candidates.sort(key=lambda r: Q(r['q']))
            write(OUT/'candidate_summary.json', dict(candidates=candidates, frozen_before_final_source=True))
            fixed = {r['file']: (OUT/r['file']).read_bytes() for r in candidates}
            programs = [p for r in candidates for p in json.loads(fixed[r['file']])['programs']]
            eligible = [p for p in programs if p['final_eligible']]
            final_phase, final, peak3 = None, [], 0
            if eligible:
                final_data, final_phase = source_phase('final', scales(SPEC['final_k_anchors']))
                del final_data
                final, peak3 = collect(pool, final_task, eligible, start, 'prime_moment_final_checked')
            else:
                write(OUT/'final_skipped.json', dict(reason='No selected program passed both known lemmas.',
                      new_final_source_queries=0, diagnostic_tests_of_refuted_programs=0))
        for name, content in fixed.items():
            if (OUT/name).read_bytes() != content:
                raise ValueError('frozen candidate changed')
        if (OUT/'learning_data.json').read_bytes() != learning_bytes:
            raise ValueError('admitted learning source changed')
        for name, content in frozen.items():
            if (ROOT/name).read_bytes() != content:
                raise ValueError('frozen075 source changed ' + name)
        validate_parent()
        final_index = {r['id']: r for r in final}
        dispositions = []
        for item in programs:
            last = final_index.get(item['id'], {}).get('evaluation', item['adaptation'])
            dispositions.append(dict(id=item['id'], q=item['program']['q'], kind=item['selection']['kind'],
                parent_record=item['parent_record'], final_evaluated=item['id'] in final_index,
                status=last['status'], direct_correlation_proved=last['universal_direct_correlation_proved'],
                unpaid_leaves=SEARCH.next_obligations(item, last), uniform_source_bound_proved=False))
        parent_peak = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        worker_peak = max((r['worker_peak_rss_kib'] for r in records+candidates+final), default=0)
        phases = [learning_phase] + ([final_phase] if final_phase else [])
        report = dict(status='PAIRED_PRIME_MOMENT_SEARCH_COMPLETE_UNIFORM_LEMMAS_OPEN',
            distinct_operator_shapes=len(dictionary), moment_controls=len(records),
            moment_correlation_refutations=sum(bool(r['adaptation_correlation']['failures']) for r in records),
            independently_checked_correlation_witnesses=sum(r['independent_witness'] is not None for r in records),
            candidate_programs=len(programs), fresh_final_programs=len(final),
            finite_survivors=sum(r['status']=='VERIFIED_ON_FINITE_DOMAIN' for r in dispositions),
            finite_refutations=sum(r['status']=='REFUTED' for r in dispositions),
            candidate_summary=candidates, dispositions=dispositions, source_phases=phases,
            producer_operations=pm.ops+sum(r['producer_operations'] for r in records+candidates+phases),
            checker_operations=sum(r['checker_operations'] for r in records+candidates+final+phases),
            sampled_parallel_rss_peak_bytes=max(peak1, peak2, peak3),
            conservative_sum_process_peaks_bytes=1024*(parent_peak+SPEC['workers']*worker_peak),
            parent_peak_rss_kib=parent_peak, largest_worker_peak_rss_kib=worker_peak,
            elapsed_seconds=time.monotonic()-start, prior_frozen_counts=counts, new_frozen_files=len(FILES),
            development_receipts=receipts, sparse_grid_samples_are_not_uniform_proofs=True,
            no_numerical_constant_refits_on_adaptation=True, hashes_used=False,
            uniform_source_bound_proved=False, uniform_head_bound_proved=False,
            uniform_core_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        write(OUT/'next_search_input.json', dict(schema='paired-prime-moment-obligations-v1',
            source_spec=SPEC['source'], lattice_domain='all integer u, G(u)=Z(u/80)',
            programs=dispositions, moment_control_files=['moment_'+r['id']+'.json' for r in records],
            complete_head_and_separable_prices_still_unpaid=True,
            uniform_arithmetic_lemmas_paid=False, RH_proved=False))
        emit('prime_moment_complete', elapsed_seconds=report['elapsed_seconds'],
             finite_survivors=report['finite_survivors'], refutations=report['finite_refutations'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', dict(type=type(exc).__name__, message=str(exc), RH_proved=False))
        raise


if __name__ == '__main__':
    main()
