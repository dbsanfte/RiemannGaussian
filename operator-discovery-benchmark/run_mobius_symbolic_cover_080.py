"""Feedback-driven complement constructions, frozen before fresh scale sampling."""
import os
for _key in ('OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'OMP_NUM_THREADS'):
    os.environ[_key] = '1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
import resource
import time

import mobius_symbolic_cover_080 as SEARCH
import check_mobius_symbolic_cover_080 as CHECK
import run_mobius_scale_flux_079 as PRIOR
from run_fractional_prime_kernel_051 import write, emit

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT/'symbolic_cover_followup_001'
FILES = ['mobius_symbolic_cover_080.py', 'test_mobius_symbolic_cover_080.py',
         'mobius_symbolic_cover_search_080_development.json', 'check_mobius_symbolic_cover_080.py',
         'test_check_mobius_symbolic_cover_080.py', 'mobius_symbolic_cover_checker_080_development.json',
         'MOBIUS_SYMBOLIC_COVER_CHECK_SCOPE_080.txt', 'MOBIUS_BOUND_CONSTRUCTION_REVIEW_080.txt',
         'mobius_symbolic_cover_protocol_080.txt', 'run_mobius_symbolic_cover_080.py']
SPEC = dict(source_ids=PRIOR.SPEC['source_ids'], gammas=PRIOR.SPEC['gammas'], q=PRIOR.SPEC['q'],
    base=6300, maximum_parent=5242880, known_arithmetic_horizon=1310720,
    primitive_support_budget=3, promoted_support_budget=4, slopes=list(SEARCH.SLOPES),
    modes=['baseline', 'promoted'], exact_shortlist=4, affine_coefficient_l1_budget=128,
    kappa_rounding_bits=40, radical_price_bits=24, log_series_terms=32,
    seed=20261011080, irregular_cases_per_band=12, workers=3,
    max_aggregate_bytes=16*1024**3, module_seconds=7200, work_limit=300_000_000_000,
    discovery_reuses079_cells=True, new_arithmetic_horizon=False,
    first_cutoff_prime_entry_boundaries=True, all_cutoff_boundaries_covered=False,
    candidates_frozen_before_validation_draw=True, uniform_correlation_proved=False,
    RH_proved=False, hashes_used=False)


def require(result, status):
    if result.get('status') != status:
        raise ValueError('080 independent admission '+str(result))
    return result


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve079 '+name)
    publication = json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve079 feedback '+name)
    return counts+[len(PRIOR.FILES), len(publication['postrun_files'])]


def feedback_rules(feedback):
    rules = {}
    for source_id in SPEC['source_ids']:
        obligations = [c for job in feedback['jobs'] if job['source_id'] == source_id
                       for c in job['proved_nuisance_mode_constraints']]
        if not obligations or any(c['supported_coordinates'] != [1, 9]
                or c['exact_symbolic_repair_condition'] != 'a1=a9*log((1-alpha)/alpha)'
                for c in obligations):
            raise ValueError('feedback must supply the supported proved mode')
        rules[source_id] = dict(coordinates=obligations[0]['supported_coordinates'],
            signature=['-1', 'L'], log_argument_formula='(3-2*gamma)/(2*gamma)',
            domain='1/2<gamma<3/4', imported_from='079/postrun_next_search_input.json',
            observed_gammas=sorted({job['gamma'] for job in feedback['jobs'] if job['source_id'] == source_id}, key=Q),
            use_proved_domain_beyond_observed_gamma=True, other_channels_unpaid=True,
            lower_logarithmic_remainders_unpaid=True)
    return rules


def known_parent_inventory():
    old076 = PRIOR.PRIOR.PRIOR.PRIOR
    records = []
    all_us = set()
    for phase in ('discovery', 'adaptation', 'final'):
        path = old076.OUT/(phase+'_data.json')
        data = json.loads(path.read_text())
        admission = json.loads((old076.OUT/(phase+'_source_admission.json')).read_text())
        old076.PRIOR.require_admitted_source(data, admission)
        values = sorted({r['u'] for r in data['rows']})
        all_us.update(values); records.append(dict(file=str(path), parents=values))
    for stage in (PRIOR.PRIOR, PRIOR):
        values = sorted(int(p.stem.removeprefix('source_')) for p in stage.OUT.glob('source_*.json')
                        if p.stem.removeprefix('source_').isdigit())
        all_us.update(values); records.append(dict(source_directory=str(stage.OUT), parents=values))
    return dict(parents=sorted(all_us), records=records,
        scope='all076 admitted parent rows and all078/079 source parents, including saved halves',
        underlying_mobius_prefix_already_known=True)


_META, _DISCOVERY, _RULES = {}, {}, {}
_ARITHMETIC = None
_INITIAL_CONSTRUCTOR, _INITIAL_CHECKER = 0, 0
_MAIN_PEAK = 0


def check_stage(start, pids=None):
    global _MAIN_PEAK
    if time.monotonic()-start > SPEC['module_seconds']:
        raise TimeoutError('080 authorized stage runtime')
    used = PRIOR.PRIOR.PRIOR.PRIOR.RESOURCES.rss(pids or [os.getpid()])
    _MAIN_PEAK = max(_MAIN_PEAK, used)
    if used > SPEC['max_aggregate_bytes']:
        raise MemoryError('080 aggregate memory')
    return used


def initialize_search(us):
    global _META, _DISCOVERY, _RULES
    _META = json.loads((OUT/'source_metadata.json').read_text())
    _RULES = json.loads((OUT/'feedback_rules.json').read_text())
    _DISCOVERY = {(id, gamma): {} for id in SPEC['source_ids'] for gamma in SPEC['gammas']}
    for u in us:
        data = json.loads((PRIOR.OUT/('source_'+str(u)+'.json')).read_text())
        for id, gammas in data['records'].items():
            if any(x['status'] != 'VERIFIED_KERNEL_ROW' for x in data['kernel_bindings'][id]):
                raise ValueError('inherited079 literal kernel binding required')
            for gamma, item in gammas.items():
                if item['cell_admission']['status'] != 'VERIFIED_CELLS' or not item['both_endpoint_residuals_recombined']:
                    raise ValueError('inherited079 independently admitted complete cells required')
                _DISCOVERY[id, gamma][u] = item


def checked_leaves(rows, rays, kappas, q, logspec, watchdog=None):
    leaves = []
    for i, (a, k) in enumerate(zip(rays, kappas)):
        checks = []
        for _, row in sorted(rows.items()):
            if watchdog is not None:
                watchdog()
            checks.append(CHECK.verify_leaf(row, a, k, q, logspec))
        if any(x['status'] not in ('CERTIFIED_FINITE', 'REFUTED_FINITE', 'UNRESOLVED_INTERVAL') for x in checks):
            raise ValueError('invalid symbolic local leaf '+str(checks))
        leaves.append(dict(index=i, ray=a, kappa=k, checks=checks,
            certified=sum(x['status'] == 'CERTIFIED_FINITE' for x in checks),
            refuted=sum(x['status'] == 'REFUTED_FINITE' for x in checks),
            unresolved=sum(x['status'] == 'UNRESOLVED_INTERVAL' for x in checks)))
    return dict(leaves=leaves, certified=sum(x['certified'] for x in leaves),
        refuted=sum(x['refuted'] for x in leaves), unresolved=sum(x['unresolved'] for x in leaves),
        checker_operations=sum(c['ops'] for x in leaves for c in x['checks']), uniform_correlation_proved=False)


def search_task(task):
    id, gamma, mode = task
    start = time.monotonic()
    meter = SEARCH.OLD.P.F.S.Meter(SPEC['work_limit'])
    meta, items = _META[id], _DISCOVERY[id, gamma]
    active = [i for i in range(10) if i not in meta['inactive_admissions'][gamma]['indices']]
    rows = {u: SEARCH.OLD.leaf_row(x['payload'], x['token_intervals']) for u, x in items.items()}
    for row in rows.values():
        if any(row['flux_features'][i] for i in range(10) if i not in active):
            raise ArithmeticError('inactive coordinate theorem disagrees with saved source')
    logspec = SEARCH.log_spec(str((3-2*Q(gamma))/(2*Q(gamma))) if Q(gamma) > Q(1, 2) else '1')
    log_admission = require(CHECK.verify_log(logspec), 'VERIFIED_LOG_ENCLOSURE')
    frames = SEARCH.generate_frames(active, mode, _RULES[id], meter)
    K = meta['norm']['certificate']['K']
    gates, rejected, accepted, checker_ops = {}, [], [], log_admission['ops']
    for frame in frames:
        meter.charge(10000)
        bad = []
        for i, a in enumerate(frame['rays']):
            key = SEARCH.ray_key(a)
            if key not in gates:
                proposal = SEARCH.mode_obstruction(meta['fixed_kernel'], meta['primes'], gamma, a, logspec)
                admission = None
                if proposal['status'] == 'SYMBOLIC_MODE_OBSTRUCTION_PROPOSAL':
                    admission = require(CHECK.verify_mode_obstruction(meta['fixed_kernel'], meta['primes'], gamma,
                        a, logspec, proposal['certificate']), 'VERIFIED_SYMBOLIC_MODE_OBSTRUCTION')
                    checker_ops += admission['ops']
                gates[key] = dict(ray=a, proposal=proposal, admission=admission)
            if gates[key]['admission'] is not None:
                bad.append(i)
        if bad:
            rejected.append(dict(frame_index=frame['index'], obstructed_leaves=bad))
        else:
            accepted.append(frame)
    # Physical coefficient types, not just numerical leaf values, witness
    # that each leaf differs from a scalar restatement of the total flux.
    forms = {u: SEARCH.physical_forms(x['payload']) for u, x in items.items()}
    witnesses = {}
    proposals, rankings = [], []
    for q in SPEC['q']:
        ranked = SEARCH.rank_frames(rows, accepted, q, K, logspec, meter=meter)
        rankings.append(dict(q=q, ranking=ranked))
        shortlist, noncircular_rejected, calibration_rejected = [], [], []
        for ranked_item in ranked:
            if time.monotonic()-start > SPEC['module_seconds']:
                raise TimeoutError('080 search task runtime')
            frame = frames[ranked_item['frame_index']]
            for a in frame['rays']:
                key = SEARCH.ray_key(a)
                if key not in witnesses:
                    witnesses[key] = None
                    for u, item in sorted(items.items(), reverse=True):
                        meter.charge(10000*len(forms[u]))
                        witness = SEARCH.noncircular_witness(item['payload'], a, logspec, forms[u])
                        if witness is not None:
                            admission = require(CHECK.verify_noncircularity(item['payload'], a, logspec,
                                witness['first_cell'], witness['second_cell']), 'VERIFIED_NONCIRCULARITY')
                            checker_ops += admission['ops']
                            witnesses[key] = dict(u=u, witness=witness, admission=admission)
                            break
            if any(witnesses[SEARCH.ray_key(a)] is None for a in frame['rays']):
                noncircular_rejected.append(frame['index']); continue
            meter.charge(100000*len(rows)*len(frame['rays']))
            calibrations = [SEARCH.calibrate(rows, a, q, logspec) for a in frame['rays']]
            if any(x is None for x in calibrations):
                calibration_rejected.append(frame['index']); continue
            kappas = [x['kappa'] for x in calibrations]
            checks = checked_leaves(rows, frame['rays'], kappas, q, logspec)
            checker_ops += checks['checker_operations']
            if checks['refuted'] or checks['unresolved']:
                raise ArithmeticError('080 exact discovery calibration did not certify')
            price = SEARCH.cover_price(frame['rays'], kappas, K, logspec)
            cover = require(CHECK.verify_cover(frame['target'], frame['rays'], kappas, K, logspec,
                dict(price=str(price))), 'VERIFIED_CONDITIONAL_COVER')
            checker_ops += cover['ops']
            promotion = None
            if mode == 'promoted':
                promotion = require(CHECK.verify_mode_annihilator(gamma, frame['rays'][0], logspec),
                                    'VERIFIED_LEADING_MODE_ANNIHILATION')
                checker_ops += promotion['ops']
            shortlist.append(dict(frame=frame, kappas=kappas, calibrations=calibrations,
                noncircularity=[witnesses[SEARCH.ray_key(a)] for a in frame['rays']],
                logspec=logspec, log_admission=log_admission, cover_admission=cover,
                certificate=dict(price=str(price)), promotion_admission=promotion,
                discovery_checks=checks, approximate_price=ranked_item['approximate_price']))
            if len(shortlist) == SPEC['exact_shortlist']:
                break
        best = min(shortlist, key=lambda x: (Q(x['certificate']['price']), x['frame']['index'])) if shortlist else None
        proposals.append(dict(source_id=id, gamma=gamma, mode=mode, q=q,
            status='CONDITIONAL_COVER_PROPOSAL' if best else 'NO_ADMISSIBLE_COVER', best=best,
            exact_shortlist=shortlist, noncircularity_rejections=noncircular_rejected,
            calibration_rejections=calibration_rejected, global_optimum_claimed=False))
    name = 'proposal_'+id+'_'+gamma.replace('/', '_')+'_'+mode+'.json'
    result = dict(source_id=id, gamma=gamma, mode=mode, generated_frames=len(frames),
        all_frames=frames, structural_rejections=rejected, symbolic_mode_checks=list(gates.values()),
        rankings=rankings, proposals=proposals, constructor_operations=meter.ops,
        checker_operations=checker_ops, elapsed_seconds=time.monotonic()-start,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/name, result)
    compact = []
    for p in proposals:
        if p['best']:
            compact.append(dict(source_id=id, gamma=gamma, mode=mode, q=p['q'],
                **{k: v for k, v in p['best'].items() if k != 'discovery_checks'}))
    return dict(file=name, source_id=id, gamma=gamma, mode=mode, proposals=compact,
        generated_frames=len(frames), structural_rejections=len(rejected),
        constructor_operations=meter.ops, checker_operations=checker_ops,
        worker_peak_rss_kib=result['worker_peak_rss_kib'])


def initialize_source(maximum):
    global _ARITHMETIC, _META, _INITIAL_CONSTRUCTOR, _INITIAL_CHECKER
    _ARITHMETIC = SEARCH.OLD.P.Arithmetic(maximum)
    meter = CHECK.Meter()
    CHECK.F.A.ensure_horizon(maximum, meter)
    _INITIAL_CONSTRUCTOR, _INITIAL_CHECKER = _ARITHMETIC.meter.ops, meter.ops
    _META = json.loads((OUT/'source_metadata.json').read_text())


def source_task(task):
    global _INITIAL_CONSTRUCTOR, _INITIAL_CHECKER
    u, gammas = task
    start = time.monotonic()
    meter = SEARCH.OLD.P.F.S.Meter(SPEC['work_limit'])
    meter.charge(_INITIAL_CONSTRUCTOR); _INITIAL_CONSTRUCTOR = 0
    checker_ops = _INITIAL_CHECKER; _INITIAL_CHECKER = 0
    _ARITHMETIC.meter = meter
    if not 2*SPEC['base'] <= u <= SPEC['maximum_parent']:
        raise ValueError('declared parent domain')
    records = {}
    for id in SPEC['source_ids']:
        meta = _META[id]
        parent, child = [SEARCH.kernel_intervals(meta['norm']['folded_kernel'], v) for v in (u, u//2)]
        records[id] = {}
        for gamma in gammas:
            payload = SEARCH.OLD.construct_cells(_ARITHMETIC, u, parent, child, meta['primes'], gamma)
            cells = require(CHECK.F.verify_cells(parent, child, meta['primes'], gamma, payload), 'VERIFIED_CELLS')
            binding = require(CHECK.verify_source_pair(meta['fixed_kernel'], meta['primes'], u,
                parent, child, payload), 'VERIFIED_SOURCE_PAIR')
            if any(payload['flux_features'][i] for i in meta['inactive_admissions'][gamma]['indices']):
                raise ArithmeticError('fresh source inactive coordinate identity failed')
            records[id][gamma] = dict(payload=payload, token_intervals={'1': ['1', '1']},
                parent_intervals=parent, child_intervals=child, cell_admission=cells, source_pair_admission=binding)
            checker_ops += cells['ops']+binding['ops']
    result = dict(u=u, child_u=u//2, records=records, constructor_operations=meter.ops,
        checker_operations=checker_ops, elapsed_seconds=time.monotonic()-start,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        fresh_parent_case=True, new_arithmetic_horizon=False)
    write(OUT/('source_'+str(u)+'.json'), result)
    return {k: v for k, v in result.items() if k != 'records'}


def pool_tasks(function, tasks, initializer, initargs, start, label):
    results, peak, last = [], 0, time.monotonic()
    with mp.get_context('spawn').Pool(SPEC['workers'], initializer=initializer, initargs=initargs) as pool:
        iterator = pool.imap_unordered(function, tasks, chunksize=1)
        while len(results) < len(tasks):
            used = check_stage(start, [os.getpid()]+[p.pid for p in pool._pool])
            peak = max(peak, used)
            if used > SPEC['max_aggregate_bytes']:
                raise MemoryError('080 aggregate memory')
            try:
                item = iterator.next(timeout=1)
            except mp.TimeoutError:
                continue
            results.append(item)
            if len(results) == len(tasks) or time.monotonic()-last > 15:
                emit(label, completed=len(results), total=len(tasks)); last = time.monotonic()
    return results, peak


def main():
    if OUT.exists():
        raise FileExistsError('preserve every080 scientific attempt')
    start = time.monotonic()
    counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    for name, content in frozen.items():
        if name.endswith('_development.json') and json.loads(content)['status'] != 'PASS':
            raise ValueError('080 development must pass before science')
    meta = json.loads((PRIOR.OUT/'source_metadata.json').read_text())
    for m in meta.values():
        require(m['source_binding'], 'VERIFIED_FIXED_KERNEL')
        require(m['norm_admission'], 'VERIFIED_UNIFORM_COEFFICIENT_NORM')
        require(m['complete_base'], 'VERIFIED_COMPLETE_BASE')
        if m['norm_admission']['folded_kernel'] != m['norm']['folded_kernel'] or m['primes'] != [2, 3, 5, 7]:
            raise ValueError('fixed source/prime domain binding')
        for gamma in SPEC['gammas']:
            require(m['inactive_admissions'][gamma], 'VERIFIED_INACTIVE_COORDINATES')
    rules = feedback_rules(json.loads((PRIOR.OUT/'postrun_next_search_input.json').read_text()))
    discovery = PRIOR.parents(PRIOR.SPEC['discovery_k'])
    inventory = known_parent_inventory()
    check_stage(start)
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, content in frozen.items():
        with (OUT/'source_snapshot'/name).open('xb') as f:
            f.write(content)
    try:
        write(OUT/'spec.json', dict(spec=SPEC, discovery_parents=discovery, prior_frozen_counts=counts,
            new_frozen_files=len(FILES), no_validation_draw_yet=True))
        write(OUT/'source_metadata.json', meta); write(OUT/'feedback_rules.json', rules)
        write(OUT/'known_parent_inventory.json', inventory)
        tasks = [(id, gamma, mode) for id in SPEC['source_ids'] for gamma in SPEC['gammas']
                 for mode in SPEC['modes'] if mode == 'baseline' or Q(gamma) > Q(1, 2)]
        proposals, peak1 = pool_tasks(search_task, tasks, initialize_search, (discovery,), start, 'symbolic_construction_search')
        candidates = []
        for id in SPEC['source_ids']:
            for q in SPEC['q']:
                for mode in SPEC['modes']:
                    options = [dict(p, proposal_file=x['file']) for x in proposals for p in x['proposals']
                               if p['source_id'] == id and p['q'] == q and p['mode'] == mode]
                    if not options:
                        continue
                    best = min(options, key=lambda p: (Q(p['certificate']['price']), Q(p['gamma']), p['frame']['index']))
                    best.update(id=id+'_q'+q.replace('/', '_')+'_'+mode, frozen_before_validation_draw=True,
                        all_uniform_covariance_leaves_unpaid=True, uniform_source_bound_proved=False, RH_proved=False)
                    filename = 'candidate_'+best['id']+'.json'; write(OUT/filename, best)
                    candidates.append((best, (OUT/filename).read_bytes()))
        write(OUT/'frozen_candidates.json', dict(candidates=[x for x, _ in candidates], validation_draw_started=False))
        needed = sorted({x['gamma'] for x, _ in candidates}, key=Q)
        draw = SEARCH.validation_draw(needed, SPEC['maximum_parent'], SPEC['base'], SPEC['seed'],
            SPEC['irregular_cases_per_band'], inventory['parents']) if candidates else dict(parents=[], draws=[])
        write(OUT/'validation_draw.json', draw)
        validation = draw['parents']
        if set(validation) & set(inventory['parents']):
            raise ValueError('fresh parent overlaps registered known data')
        data, peak2 = pool_tasks(source_task, [(u, needed) for u in validation], initialize_source,
            (max(validation)//4,), start, 'symbolic_fresh_cells') if validation else ([], 0)
        results, checker_ops = [], 0
        for candidate, immutable in candidates:
            check_stage(start)
            rows = {}
            for u in validation:
                check_stage(start)
                item = json.loads((OUT/('source_'+str(u)+'.json')).read_text())['records'][candidate['source_id']][candidate['gamma']]
                require(item['cell_admission'], 'VERIFIED_CELLS'); require(item['source_pair_admission'], 'VERIFIED_SOURCE_PAIR')
                rows[u] = SEARCH.OLD.leaf_row(item['payload'], item['token_intervals'])
            checks = checked_leaves(rows, candidate['frame']['rays'], candidate['kappas'], candidate['q'], candidate['logspec'],
                                    watchdog=lambda: check_stage(start))
            checker_ops += checks['checker_operations']
            if (OUT/('candidate_'+candidate['id']+'.json')).read_bytes() != immutable:
                raise ValueError('080 candidate changed after validation')
            write(OUT/('validation_checks_'+candidate['id']+'.json'), checks)
            write(OUT/('diagnostics_'+candidate['id']+'.json'), dict(rows=[SEARCH.diagnostics(row,
                candidate['frame']['rays'], candidate['logspec']) for _, row in sorted(rows.items())],
                numerical_diagnostic_only=True, lower_logarithmic_remainders_unpaid=True))
            failures = [dict(leaf_index=x['index'], ray=x['ray'], kappa=x['kappa'], refuted=x['refuted'],
                first_witness=next(c for c in x['checks'] if c['status'] == 'REFUTED_FINITE')) for x in checks['leaves'] if x['refuted']]
            result = dict(id=candidate['id'], source_id=candidate['source_id'], q=candidate['q'], mode=candidate['mode'],
                gamma=candidate['gamma'], conditional_flux_price=candidate['certificate']['price'],
                certified=checks['certified'], refuted=checks['refuted'], unresolved=checks['unresolved'],
                leaf_failures=failures, finite_status='REFUTED_LOCAL_BOUND' if checks['refuted'] else
                'UNRESOLVED_INTERVAL' if checks['unresolved'] else 'FINITE_ONLY',
                arithmetic_residual_refuted=False, uniform_correlation_proved=False, RH_proved=False)
            results.append(result); emit('symbolic_cover_validation', id=result['id'], refuted=result['refuted'])
        for name, content in frozen.items():
            if (ROOT/name).read_bytes() != content:
                raise ValueError('080 frozen source changed '+name)
        validate_parent(); check_stage(start)
        all_work = proposals+data
        report = dict(status='SYMBOLIC_COMPLEMENT_SEARCH_COMPLETE', results=results,
            generated_frames=sum(x['generated_frames'] for x in proposals),
            structurally_obstructed_frames=sum(x['structural_rejections'] for x in proposals),
            source_mode_gamma_jobs=len(proposals), frozen_candidates=len(candidates), discovery_parents=len(discovery),
            fresh_validation_parents=len(validation), independently_reconstructed_cell_rows=len(data)*len(needed)*len(SPEC['source_ids']),
            constructor_operations=sum(x['constructor_operations'] for x in all_work),
            checker_operations=sum(x['checker_operations'] for x in all_work)+checker_ops,
            elapsed_seconds=time.monotonic()-start, sampled_parallel_rss_peak_bytes=max(peak1, peak2, _MAIN_PEAK),
            conservative_sum_process_peaks_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
                SPEC['workers']*max((x['worker_peak_rss_kib'] for x in all_work), default=0)),
            prior_frozen_counts=counts, new_frozen_files=len(FILES), hashes_used=False,
            uniform_correlation_proved=False, uniform_residual_bound_proved=False, uniform_head_bound_proved=False,
            uniform_core_bound_proved=False, new_arithmetic_horizon=False, RH_proved=False)
        write(OUT/'next_search_input.json', dict(schema='symbolic-complement-bound-feedback-v1', results=results,
            paid='exact affine complement identity, independent finite source/cells, conditional price, inherited coefficient norm and complete base',
            unpaid='both uniform signed covariance leaves, unknown cross-channel signatures and lower-logarithmic remainders',
            next_mechanisms=['joint cross-channel signed controls', 'higher-mode annihilation with explicit remainder argument',
                             'auxiliary recurrences that control both complementary leaves'],
            do_not_just_increase_kappa=True, finite_survival_is_not_uniform_control=True,
            original_source_head_core_RH_transfer_still_required=True, RH_proved=False))
        check_stage(start)
        report['elapsed_seconds'] = time.monotonic()-start
        write(OUT/'report.json', report)
        check_stage(start)
        emit('symbolic_search_complete', candidates=len(candidates), elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', dict(type=type(exc).__name__, message=str(exc), RH_proved=False))
        raise


if __name__ == '__main__': main()
