"""Obligation-driven signed packet invention with frozen fresh validation."""
import os
for _key in ('OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'OMP_NUM_THREADS'):
    os.environ[_key] = '1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
import resource
import time

import mobius_density_packet_081 as SEARCH
import check_mobius_density_packet_081 as CHECK
import run_mobius_symbolic_cover_080 as PRIOR
from run_fractional_prime_kernel_051 import write, emit

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT/'density_packet_followup_001'
FILES = ['mobius_density_packet_081.py', 'test_mobius_density_packet_081.py',
    'mobius_density_packet_search_081_development.json', 'check_mobius_density_packet_081.py',
    'test_check_mobius_density_packet_081.py', 'mobius_density_packet_checker_081_development.json',
    'MOBIUS_DENSITY_PACKET_CHECK_SCOPE_081.txt', 'MOBIUS_JOINT_RECURRENCE_DESIGN_081.txt',
    'mobius_density_packet_protocol_081.txt', 'run_mobius_density_packet_081.py']
SPEC = dict(source_ids=PRIOR.SPEC['source_ids'], maximum_parent=5242880, arithmetic_horizon=1310720,
    discovery_stride_in080=8, q='1', drift_multiplier='3/2', memory_maximum=3,
    ray_tail_values=['-1', '0', '1'], gram_weights=['1/4', '1'],
    epsilon_minimum='1/8', epsilon_maximum='1/2', epsilon_denominator_budget=8,
    eta_fractions_of_proved_limit=['1/2', '3/4', '1'],
    selection_tracks=['largest_growing_roster', 'smallest_paid_constant', 'smallest_observed_unlinked'],
    selection_requires_two_density_signs=True, selection_requires_nonzero_packet=True,
    selection_requires_memory_cross_term=True, zero_padded_memory_duplicates_removed=True,
    seed=20261011081, fresh_irregular_per_band=3, workers=3, native_threads=1,
    max_aggregate_bytes=16*1024**3, module_seconds=7200, work_limit=300_000_000_000,
    new_arithmetic_horizon=False, old080_validation_now_explicitly_discovery=True,
    exact_compilation_is_not_a_uniform_source_bound=True, uniform_unlinked_bound_proved=False,
    candidates_frozen_before_validation_draw=True, hashes_used=False, RH_proved=False)


def require(result, status):
    if result.get('status') != status:
        raise ValueError('081 independent admission '+str(result))
    return result


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve080 '+name)
    publication = json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve080 feedback '+name)
    return counts+[len(PRIOR.FILES), len(publication['postrun_files'])]


def parent_inventory():
    inventory = PRIOR.known_parent_inventory()
    known = set(inventory['parents'])
    current = json.loads((PRIOR.OUT/'validation_draw.json').read_text())['parents']
    for u in current:
        known.add(u)
        known.add(u//2)  # both endpoints were actually queried in080
    known.update((1103, 551, 275))  # real-kernel development integration and delays
    return dict(parents=sorted(known), prior_inventory=inventory,
        newly_registered080_parents=current, included080_halves=True,
        development_original_source_parents=[1103, 551, 275],
        scope='all076/078/079 registered parents and saved halves, plus080 parents and halves',
        underlying_mobius_prefix_already_known=True)


_PEAK = 0
_META, _DISCOVERY, _ARITHMETIC = {}, [], None
_INIT_OPS = 0


def check_stage(start, pids=()):
    global _PEAK
    if time.monotonic()-start > SPEC['module_seconds']:
        raise TimeoutError('081 authorized stage runtime')
    total = 0
    for pid in pids or [os.getpid()]:
        try:
            with open('/proc/'+str(pid)+'/status') as f:
                total += next((int(line.split()[1])*1024 for line in f if line.startswith('VmRSS:')), 0)
        except FileNotFoundError:
            pass
    _PEAK = max(_PEAK, total)
    if total > SPEC['max_aggregate_bytes']:
        raise MemoryError('081 aggregate memory')
    return total


def initialize(discovery, horizon, construct=True):
    global _META, _DISCOVERY, _ARITHMETIC, _INIT_OPS
    _META = json.loads((OUT/'source_metadata.json').read_text())
    _DISCOVERY = discovery
    if construct:
        _ARITHMETIC = SEARCH.Arithmetic(horizon)
        _INIT_OPS = _ARITHMETIC.meter.ops


def make_program(source_id, energy, schedule):
    return dict(schema='growing-density-packet-v1', kernel=_META[source_id]['fixed_kernel'],
        memory=energy['memory'], rays=energy['rays'], drift_multiplier=SPEC['drift_multiplier'], **schedule)


def search_task(task):
    global _INIT_OPS
    source_id, energy = task
    start = time.monotonic()
    meter = _ARITHMETIC.meter
    initial = meter.ops
    schedules = SEARCH.proof_schedules()
    programs = [make_program(source_id, energy, schedule) for schedule in schedules]
    maximum = max(SEARCH.OLD.floor_power(max(_DISCOVERY), p['eta']) for p in programs)
    bank = SEARCH.PairBank(programs[0], maximum, _ARITHMETIC)
    rows = {}
    for u in sorted(_DISCOVERY, reverse=True):
        check_stage(start)
        Ds = sorted({SEARCH.OLD.floor_power(u, p['eta']) for p in programs})
        bank.packet_values(u, Ds)
        matching = {SEARCH.OLD.floor_power(u, p['eta']): p for p in programs}
        rows[str(u)] = {str(D): bank.finite_certificate(matching[D], u) for D in Ds}
    proposals = []
    checker_ops = 0
    for index, p in enumerate(programs):
        certificate = SEARCH.bound_certificate(p, meter)
        admission = require(CHECK.verify_bound(p, certificate), 'VERIFIED_UNIFORM_SIGNED_PACKET_BOUND')
        checker_ops += admission['ops']
        selected_rows = [rows[str(u)][str(SEARCH.OLD.floor_power(u, p['eta']))] for u in _DISCOVERY]
        ratios = [Q(row['unlinked'])/u for u, row in zip(_DISCOVERY, selected_rows)]
        calibrated = SEARCH.ceil24(max([Q(0)]+ratios))
        nonzero_packet = any(Q(row['packet']) for row in selected_rows)
        both_signs = any(Q(row['positive_mass']) > 0 and Q(row['negative_mass']) > 0 for row in selected_rows)
        qualifies = energy['kind'] == 'memory_cross_term' and nonzero_packet and both_signs
        proposals.append(dict(source_id=source_id, energy_index=energy['index'], schedule_index=index,
            energy_kind=energy['kind'], program=p, certificate=certificate, bound_admission=admission,
            selection_eligible=qualifies, nonzero_packet_seen=nonzero_packet, both_density_signs_seen=both_signs,
            discovery_unlinked_kappa=str(calibrated), maximum_observed_unlinked_over_u=str(max(ratios)),
            positive_packet_rows=sum(Q(row['packet']) > 0 for row in selected_rows),
            negative_packet_rows=sum(Q(row['packet']) < 0 for row in selected_rows),
            maximum_D=max(row['D'] for row in selected_rows),
            unlinked_kappa_is_finite_calibration_only=True, uniform_unlinked_bound_proved=False))
    file = 'search_'+source_id+'_energy_'+str(energy['index']).zfill(2)+'.json'
    data = dict(source_id=source_id, energy=energy, all_programs=proposals,
        exact_discovery_rows_by_parent_and_D=rows, structural_witnesses=bank.witness(maximum),
        reused080_parent_data=True, constructor_operations=meter.ops-initial+_INIT_OPS,
        checker_operations=checker_ops, elapsed_seconds=time.monotonic()-start,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        weighted_pairs_means_retained_nonzero_ratio_labels=True, uniform_original_source_bound_proved=False, RH_proved=False)
    _INIT_OPS = 0
    write(OUT/file, data)
    return dict(file=file, proposals=proposals, constructor_operations=data['constructor_operations'],
        checker_operations=checker_ops, elapsed_seconds=data['elapsed_seconds'], worker_peak_rss_kib=data['worker_peak_rss_kib'])


def discovery_check_task(candidate):
    start = time.monotonic()
    data = json.loads((OUT/candidate['search_file']).read_text())
    p = candidate['program']
    rows, checks = [], []
    for u in sorted(_DISCOVERY, reverse=True):
        check_stage(start)
        cert = data['exact_discovery_rows_by_parent_and_D'][str(u)][str(SEARCH.OLD.floor_power(u, p['eta']))]
        rows.append(dict(u=u, certificate=cert))
        checks.append(require(CHECK.verify_finite(p, u, cert), 'VERIFIED_FINITE_PACKET'))
    pair_checks = []
    for witness in data['structural_witnesses'].values():
        if witness['b'] > candidate['maximum_D']:
            continue
        pair_checks.append(require(CHECK.audit_pair(p, witness['a'], witness['b']), 'VERIFIED_PAIR_KERNEL'))
    result = dict(id=candidate['id'], rows=rows, checks=checks, pair_witness_checks=pair_checks,
        checker_operations=sum(c['ops'] for c in checks+pair_checks), constructor_operations=0,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        elapsed_seconds=time.monotonic()-start, uniform_unlinked_bound_proved=False)
    write(OUT/('discovery_checks_'+candidate['id']+'.json'), result)
    return {k: v for k, v in result.items() if k not in ('rows', 'checks', 'pair_witness_checks')}


def validation_task(task):
    global _INIT_OPS
    candidate, us = task
    start = time.monotonic()
    meter = _ARITHMETIC.meter
    initial = meter.ops
    p = candidate['program']
    maximum = SEARCH.OLD.floor_power(max(us), p['eta'])
    bank = SEARCH.PairBank(p, maximum, _ARITHMETIC)
    rows, checks = [], []
    for u in sorted(us, reverse=True):
        check_stage(start)
        cert = bank.finite_certificate(p, u)
        checked = require(CHECK.verify_finite(p, u, cert), 'VERIFIED_FINITE_PACKET')
        finite = Q(cert['unlinked']) <= Q(candidate['discovery_unlinked_kappa'])*u
        # The q=1 pilot makes both inequalities exact rational comparisons.
        if abs(Q(cert['packet'])) > Q(candidate['certificate']['constant'])*u:
            raise ArithmeticError('finite packet contradicts its reviewed uniform theorem')
        rows.append(dict(u=u, certificate=cert, unlinked_calibrated_bound_holds=finite))
        checks.append(checked)
    result = dict(id=candidate['id'], rows=rows, checks=checks,
        finite_unlinked_refutations=sum(not row['unlinked_calibrated_bound_holds'] for row in rows),
        finite_unlinked_certified=sum(row['unlinked_calibrated_bound_holds'] for row in rows),
        first_refutation=next((row for row in sorted(rows, key=lambda r: r['u']) if not row['unlinked_calibrated_bound_holds']), None),
        maximum_observed_unlinked_over_u=str(max(Q(row['certificate']['unlinked'])/row['u'] for row in rows)),
        positive_packet_rows=sum(Q(row['certificate']['packet']) > 0 for row in rows),
        negative_packet_rows=sum(Q(row['certificate']['packet']) < 0 for row in rows),
        constructor_operations=meter.ops-initial+_INIT_OPS, checker_operations=sum(c['ops'] for c in checks),
        elapsed_seconds=time.monotonic()-start, worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        packet_control_scope='reviewed all-u algorithm plus independent exact certificate prices; finite compiler/source checked here',
        uniform_unlinked_bound_proved=False, original_source_head_core_RH_transfer_still_required=True, RH_proved=False)
    _INIT_OPS = 0
    write(OUT/('validation_'+candidate['id']+'.json'), result)
    return {k: v for k, v in result.items() if k not in ('rows', 'checks')}


def pool_tasks(function, tasks, initializer_args, start, label):
    results, last = [], time.monotonic()
    with mp.get_context('spawn').Pool(SPEC['workers'], initializer=initialize, initargs=initializer_args) as pool:
        iterator = pool.imap_unordered(function, tasks, chunksize=1)
        while len(results) < len(tasks):
            check_stage(start, [os.getpid()]+[p.pid for p in pool._pool])
            try:
                results.append(iterator.next(timeout=1))
            except mp.TimeoutError:
                continue
            if len(results) == len(tasks) or time.monotonic()-last > 15:
                emit(label, completed=len(results), total=len(tasks))
                last = time.monotonic()
    return results


def select_candidates(results):
    selected = []
    for source_id in SPEC['source_ids']:
        options = [dict(p, search_file=result['file']) for result in results for p in result['proposals']
                   if p['source_id'] == source_id and p['selection_eligible']]
        if not options:
            continue
        choices = [min(options, key=lambda p: (-Q(p['program']['eta']), Q(p['certificate']['constant']),
                      Q(p['discovery_unlinked_kappa']), p['energy_index'], p['schedule_index'])),
                   min(options, key=lambda p: (Q(p['certificate']['constant']), Q(p['discovery_unlinked_kappa']),
                      -Q(p['program']['eta']), p['energy_index'], p['schedule_index'])),
                   min(options, key=lambda p: (Q(p['discovery_unlinked_kappa']), -Q(p['program']['eta']),
                      Q(p['certificate']['constant']), p['energy_index'], p['schedule_index']))]
        dedup = {}
        for track, candidate in zip(SPEC['selection_tracks'], choices):
            key = candidate['energy_index'], candidate['schedule_index']
            if key not in dedup:
                dedup[key] = dict(candidate, selection_tracks=[])
            dedup[key]['selection_tracks'].append(track)
        for index, candidate in enumerate(dedup.values()):
            candidate.update(id=source_id+'_packet_'+str(index), frozen_before_validation_draw=True,
                source_kernel_binding='exact original unfolded080 fixed_kernel; no excluded-prime fold in081 representation',
                uniform_original_source_bound_proved=False, RH_proved=False)
            selected.append(candidate)
    return selected


def next_obligation(candidate):
    return dict(id=candidate['id'], source_id=candidate['source_id'], program=candidate['program'],
        exact_identity='E(u)-r*E(floor(u/2)) = W(u)+U(u)',
        packet_definition='all reduced squarefree a<b<=floor(u^eta), gcd(a,b)=1; kernel2*f(a*g)^T*T*f(b*g); min-density-bucket weights; actual mu(a)mu(b)mu(g)^2 withgcd(g,ab)=1',
        paid=dict(bound='abs(W(u))<=C_W*u for every positive integer u', C_W=candidate['certificate']['constant'],
            prerequisites=['reviewed elementary squarefree-coprime count lemma', 'reviewed all-u compiler/balance algebra', 'independent exact price certificate']),
        unpaid=dict(target='U(u)<=K*u for every positive integer u, some finiteK independentofu',
            finite_discovery_K=candidate['discovery_unlinked_kappa'], finite_K_is_not_a_proof=True,
            U_includes='diagonal + all unselected off-diagonal ratios + fractions1-w of selected ratios'),
        gcd_frontier='write m=a*g,n=b*g withgcd(a,b)=1: g>=2 reducesradius; primitiveg=1 remains atcurrentradius',
        conditional_transfer='if U<=K*u uniformly, E(u)/u<=3/4*E(floor(u/2))/floor(u/2)+C_W+K; handleu=1 directly fromR(0)=0; bound4*max(0,C_W+K)',
        full_source_head_core_parameter_transfer_unpaid=True, uniform_unlinked_bound_proved=False, RH_proved=False)


def main():
    if OUT.exists():
        raise FileExistsError('preserve every081 attempt')
    start = time.monotonic()
    counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    for name, content in frozen.items():
        if name.endswith('_development.json') and json.loads(content)['status'] != 'PASS':
            raise ValueError('081 development incomplete')
    metadata = json.loads((PRIOR.OUT/'source_metadata.json').read_text())
    for source_id in SPEC['source_ids']:
        meta = metadata[source_id]
        require(meta['source_binding'], 'VERIFIED_FIXED_KERNEL')
        if meta['source_binding']['normalized_derived_kernel'] != meta['fixed_kernel']:
            raise ValueError('inherited original kernel binding')
    feedback = json.loads((PRIOR.OUT/'postrun_next_search_input.json').read_text())
    if not feedback['first_mode_nullspace_is_necessary_not_sufficient'] or not feedback['selected_method_obstructions']:
        raise ValueError('081 requires080 coupled-remainder feedback')
    old = json.loads((PRIOR.OUT/'validation_draw.json').read_text())['parents']
    discovery = sorted(set(old[::SPEC['discovery_stride_in080']]+[old[-1]]))
    inventory = parent_inventory()
    check_stage(start)
    OUT.mkdir()
    (OUT/'source_snapshot').mkdir()
    for name, data in frozen.items():
        with (OUT/'source_snapshot'/name).open('xb') as f:
            f.write(data)
    try:
        write(OUT/'spec.json', dict(spec=SPEC, discovery_parents=discovery, energy_grammar=SEARCH.energy_grammar(),
            proof_schedules=SEARCH.proof_schedules(), prior_frozen_counts=counts, no_validation_draw_yet=True))
        write(OUT/'source_metadata.json', metadata)
        write(OUT/'input_obstruction.json', feedback)
        write(OUT/'known_parent_inventory.json', inventory)
        tasks = [(id, energy) for id in SPEC['source_ids'] for energy in SEARCH.energy_grammar()]
        results = pool_tasks(search_task, tasks, (discovery, max(discovery)//4), start, 'density_packet_search')
        selected = select_candidates(results)
        checks = pool_tasks(discovery_check_task, selected, (discovery, 1, False), start, 'selected_packet_discovery_checks') if selected else []
        candidates = []
        for candidate in selected:
            file = OUT/('candidate_'+candidate['id']+'.json')
            write(file, candidate)
            candidates.append((candidate, file.read_bytes()))
        write(OUT/'frozen_candidates.json', dict(candidates=selected, discovery_independently_checked=True,
            validation_draw_started=False, uniform_unlinked_bound_proved=False))
        draw = SEARCH.validation_draw([c['program']['eta'] for c in selected], inventory['parents'],
            SPEC['seed'], SPEC['maximum_parent'], SPEC['fresh_irregular_per_band']) if selected else dict(parents=[], draws=[])
        write(OUT/'validation_draw.json', draw)
        validation = pool_tasks(validation_task, [(c, draw['parents']) for c in selected],
            (discovery, max(draw['parents'])//4), start, 'fresh_packet_validation') if selected else []
        for candidate, data in candidates:
            if (OUT/('candidate_'+candidate['id']+'.json')).read_bytes() != data:
                raise ValueError('081 frozen candidate changed')
        for name, data in frozen.items():
            if (ROOT/name).read_bytes() != data:
                raise ValueError('081 frozen source changed '+name)
        validate_parent()
        check_stage(start)
        all_work = results+checks+validation
        report = dict(status='GROWING_SIGNED_DENSITY_PACKET_SEARCH_COMPLETE', generated_programs=sum(len(r['proposals']) for r in results),
            generated_energy_forms=len(SEARCH.energy_grammar()), proof_schedules=len(SEARCH.proof_schedules()),
            all_generated_uniform_packet_prices_independently_checked=True,
            selected_candidates=len(selected), selected_tracks=sum(len(c['selection_tracks']) for c in selected),
            discovery_parents=len(discovery), fresh_validation_parents=len(draw['parents']),
            independently_checked_finite_rows=len(selected)*(len(discovery)+len(draw['parents'])),
            results=validation, constructor_operations=sum(r['constructor_operations'] for r in all_work),
            checker_operations=sum(r['checker_operations'] for r in all_work), elapsed_seconds=time.monotonic()-start,
            sampled_parallel_rss_peak_bytes=_PEAK, conservative_sum_process_peaks_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+
                SPEC['workers']*max((r['worker_peak_rss_kib'] for r in all_work), default=0)),
            prior_frozen_counts=counts, new_frozen_files=len(FILES), hashes_used=False,
            new_arithmetic_horizon=False, uniform_unlinked_bound_proved=False, uniform_original_source_bound_proved=False,
            reviewed_analytic_proof_is_not_a_formal_theorem_prover=True, RH_proved=False)
        if report['constructor_operations']+report['checker_operations'] > SPEC['work_limit']:
            raise RuntimeError('081 stage aggregate work proxy limit')
        write(OUT/'next_search_input.json', dict(schema='joint-density-packet-bound-feedback-v1',
            obligations=[next_obligation(c) for c in selected],
            next_mechanisms=['control the current-radius primitive coprime-pair frontier',
                'combine several paid packets with diagonal or nonpositive terms in an exact full drift decomposition',
                'seek signed cofactor recurrences with paid uniform child correlations'],
            eligible_label_retention_is_not_dense_pair_coverage=True,
            do_not_just_raise_finite_K=True, current_dense_frontier_unpaid=True, RH_proved=False))
        check_stage(start)
        report['elapsed_seconds'] = time.monotonic()-start
        report['sampled_parallel_rss_peak_bytes'] = _PEAK
        write(OUT/'report.json', report)
        check_stage(start)
        emit('density_packet_search_complete', programs=report['generated_programs'], candidates=len(selected), seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', dict(type=type(exc).__name__, message=str(exc), RH_proved=False))
        raise


if __name__ == '__main__':
    main()
