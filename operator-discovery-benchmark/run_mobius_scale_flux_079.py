"""Preregistered local signed-covariance discovery and exact cover validation."""
import os
for _key in ('OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'OMP_NUM_THREADS'):
    os.environ[_key] = '1'
import json
import multiprocessing as mp
from fractions import Fraction as Q
import resource
import time

import mobius_scale_flux_079 as SEARCH
import check_mobius_scale_flux_079 as CHECK
import check_mobius_prime_mass_gate_078 as MASS_CHECK
import run_mobius_rough_energy_078 as PRIOR
from run_fractional_prime_kernel_051 import write, emit

ROOT = PRIOR.ROOT
OUT = PRIOR.OUT/'scale_flux_followup_001'
FILES = ['mobius_scale_flux_079.py', 'test_mobius_scale_flux_079.py',
         'mobius_scale_flux_search_079_development.json', 'check_mobius_scale_flux_079.py',
         'test_check_mobius_scale_flux_079.py', 'mobius_scale_flux_checker_079_development.json',
         'MOBIUS_SCALE_FLUX_CHECK_SCOPE_079.txt', 'MOBIUS_SCALE_FLUX_REVIEW_079.txt',
         'mobius_scale_flux_protocol_079.txt', 'run_mobius_scale_flux_079.py']
SPEC = dict(source_ids=['q1_p16', 'q1_p04'], gammas=SEARCH.P.rational_grid('1/7', '2/3', 9),
    q=['1', '129/128', '33/32'], base=6300, discovery_k=[256, 512, 1024, 2048, 4096],
    validation_k=[192, 384, 768, 1536, 3072, 6144, 8192, 16384, 32768, 65536],
    phases=list(range(0, 80, 5))+[79], pair_slopes=['-2', '-1', '-1/2', '1/2', '1', '2'],
    maximum_leaf_support=2, kappa_rounding_bits=40, radical_price_bits=24,
    workers=3, work_limit=300_000_000_000, max_aggregate_bytes=16*1024**3,
    module_seconds=7200, known_arithmetic_horizon=1310720,
    search_uses_known076_arithmetic=True, new_arithmetic_horizon=False,
    baseline_prime_operator_preserved_outside_fixed_kernel_pilot='q1_p00',
    conditional_reduction_only=True, uniform_correlation_proved=False, RH_proved=False, hashes_used=False)


def parents(anchors):
    return sorted(80*k-phase for k in anchors for phase in SPEC['phases'])


def validate_parent():
    counts = PRIOR.validate_parent()
    for name in PRIOR.FILES:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve078 '+name)
    publication = json.loads((PRIOR.OUT/'publication_integrity.json').read_text())
    for name in publication['postrun_files']:
        if (ROOT/name).read_bytes() != (PRIOR.OUT/'postrun_snapshot'/name).read_bytes():
            raise ValueError('preserve078 feedback '+name)
    return counts+[len(PRIOR.FILES), len(publication['postrun_files'])]


def require(result, status):
    if result.get('status') != status:
        raise ValueError('079 independent admission '+str(result))
    return result


def source_metadata():
    result = {}
    for id in SPEC['source_ids']:
        old = json.loads((PRIOR.PRIOR.OUT/('construction_'+id+'.json')).read_text())
        base = old['kernel_binding']['kernel']
        if base != SEARCH.P.F.KERNEL:
            raise ValueError('original source G binding changed')
        fixed = SEARCH.MASS.fixed_kernel(base, old['program'])
        if fixed['status'] != 'FIXED_KERNEL_PROPOSAL':
            raise ValueError('pilot requires fixed prefix source')
        binding = require(MASS_CHECK.verify_kernel(base, old['program'], fixed['kernel']), 'VERIFIED_FIXED_KERNEL')
        primes = sorted(old['search']['prime_schedule'])
        norm = SEARCH.fixed_norm(fixed['kernel'], primes, SPEC['base'])
        admitted = require(CHECK.verify_coefficient_norm(fixed['kernel'], primes, SPEC['base'], norm['certificate']), 'VERIFIED_UNIFORM_COEFFICIENT_NORM')
        if admitted['folded_kernel'] != norm['folded_kernel']:
            raise ArithmeticError('independent fixed fold kernel mismatch')
        absolute_mass = sum((abs(Q(x['weight']))/x['divisor'] for x in norm['folded_kernel']), Q(0))
        base_certificate = dict(A=str(absolute_mass), B=str(2*SPEC['base']*absolute_mass**2))
        base_admission = require(CHECK.verify_complete_base(norm['folded_kernel'], SPEC['base'], base_certificate), 'VERIFIED_COMPLETE_BASE')
        inactive = {}
        for gamma in SPEC['gammas']:
            indices = SEARCH.inactive_coordinates(norm['folded_kernel'], gamma, SPEC['base'])
            inactive[gamma] = require(CHECK.verify_inactive(norm['folded_kernel'], gamma, SPEC['base'], indices), 'VERIFIED_INACTIVE_COORDINATES')
        result[id] = dict(source_id=id, fixed_kernel=fixed['kernel'], source_program=old['program'],
            source_binding=binding, primes=primes, norm=norm, norm_admission=admitted,
            complete_base=base_admission, inactive_admissions=inactive)
    return result


_ARITHMETIC = None
_META = {}
_DISCOVERY = {}
_INITIAL_CONSTRUCTOR = 0
_INITIAL_CHECKER = 0


def initialize_source(maximum):
    global _ARITHMETIC, _META, _INITIAL_CONSTRUCTOR, _INITIAL_CHECKER
    _ARITHMETIC = SEARCH.P.Arithmetic(maximum)
    meter = CHECK.Meter()
    CHECK.A.ensure_horizon(maximum, meter)
    _INITIAL_CONSTRUCTOR, _INITIAL_CHECKER = _ARITHMETIC.meter.ops, meter.ops
    _META = json.loads((OUT/'source_metadata.json').read_text())


def source_task(task):
    global _INITIAL_CONSTRUCTOR, _INITIAL_CHECKER
    u, gammas = task
    start = time.monotonic()
    meter = SEARCH.P.F.S.Meter(SPEC['work_limit'])
    meter.charge(_INITIAL_CONSTRUCTOR); _INITIAL_CONSTRUCTOR = 0
    _ARITHMETIC.meter = meter
    checker_ops = _INITIAL_CHECKER; _INITIAL_CHECKER = 0
    if u//2 < SPEC['base']:
        raise ValueError('uniform norm/inactive base not reached')
    old_parent = json.loads((PRIOR.OUT/('source_'+str(u)+'.json')).read_text())
    old_child = json.loads((PRIOR.OUT/('source_'+str(u//2)+'.json')).read_text())
    records, bindings = {}, {}
    for id in SPEC['source_ids']:
        p, c = old_parent['sources'][id], old_child['sources'][id]
        meta = _META[id]
        if sorted(p['prime_schedule']) != meta['primes'] or sorted(c['prime_schedule']) != meta['primes']:
            raise ValueError('same fixed folded prime domain required')
        checks = []
        for v, source in ((u, p), (u//2, c)):
            if source['compiled']['binding']['status'] != 'VERIFIED_IDENTITY' or source['compiled']['stencil_admission']['status'] != 'VERIFIED_IDENTITY':
                raise ValueError('historical source admission required')
            checks.append(require(CHECK.verify_kernel_row(meta['norm']['folded_kernel'], v, source['folded_intervals']), 'VERIFIED_KERNEL_ROW'))
        bindings[id] = checks
        checker_ops += sum(x['ops'] for x in checks)
        tokens = SEARCH.merge_tokens(p['compiled']['compiled'], c['compiled']['compiled'])
        records[id] = {}
        for gamma in gammas:
            payload = SEARCH.construct_cells(_ARITHMETIC, u, p['folded_intervals'], c['folded_intervals'], meta['primes'], gamma)
            admission = require(CHECK.verify_cells(p['folded_intervals'], c['folded_intervals'], meta['primes'], gamma, payload), 'VERIFIED_CELLS')
            # Independently admitted complete cells also bind each endpoint
            # residual, not merely their difference (which could hide errors).
            pv, cv = [{} for _ in range(10)], [{} for _ in range(10)]
            for cell in payload['cells']:
                band = payload['bands'][cell['band']]
                if cell['parent_category'] < 10:
                    SEARCH.add(pv[cell['parent_category']], band['parent_weight'], Q(cell['signed_count']))
                if cell['child_category'] < 10:
                    SEARCH.add(cv[cell['child_category']], band['child_weight'], Q(cell['signed_count']))
            pv, cv = [SEARCH.saved(x) for x in pv], [SEARCH.saved(x) for x in cv]
            for values, source in ((pv, p), (cv, c)):
                if SEARCH.P.sum_features(values) != source['expected_residual_polynomial']:
                    raise ArithmeticError('complete endpoint residual identity failed')
                if gamma in source['features'] and values != source['features'][gamma]:
                    raise ArithmeticError('saved078 signed feature identity failed')
            inactive = meta['inactive_admissions'][gamma]['indices']
            if any(payload['flux_features'][i] for i in inactive):
                raise ArithmeticError('uniform inactive coordinate identity failed')
            records[id][gamma] = dict(payload=payload, token_intervals=tokens, cell_admission=admission,
                both_endpoint_residuals_recombined=True, inherited078_features_compared_where_available=True)
            checker_ops += admission['ops']
    result = dict(u=u, child_u=u//2, records=records, kernel_bindings=bindings,
        constructor_operations=meter.ops, checker_operations=checker_ops,
        new_shared_index_cells_over_known_arithmetic=True, new_arithmetic_horizon=False,
        elapsed_seconds=time.monotonic()-start,
        worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    write(OUT/('source_'+str(u)+'.json'), result)
    return {k: v for k, v in result.items() if k not in ('records', 'kernel_bindings')}


def initialize_search(us):
    global _META, _DISCOVERY
    _META = json.loads((OUT/'source_metadata.json').read_text())
    _DISCOVERY = {(id, gamma): {} for id in SPEC['source_ids'] for gamma in SPEC['gammas']}
    for u in us:
        data = json.loads((OUT/('source_'+str(u)+'.json')).read_text())
        for id, gammas in data['records'].items():
            for gamma, item in gammas.items():
                if item['cell_admission']['status'] != 'VERIFIED_CELLS':
                    raise ValueError('independently admitted shared cells required')
                _DISCOVERY[id, gamma][u] = item


def checked_leaves(cover, rows, q):
    results = []
    for index, leaf in enumerate(cover['leaves']):
        checks = [CHECK.verify_local_leaf(row, leaf['a'], leaf['kappa'], q) for _, row in sorted(rows.items())]
        if any(x['status'] not in ('CERTIFIED_FINITE', 'REFUTED_FINITE', 'UNRESOLVED_INTERVAL') for x in checks):
            raise ValueError('invalid arithmetic leaf '+str(checks))
        results.append(dict(index=index, a=leaf['a'], kappa=leaf['kappa'], checks=checks,
            certified=sum(x['status'] == 'CERTIFIED_FINITE' for x in checks),
            refuted=sum(x['status'] == 'REFUTED_FINITE' for x in checks),
            unresolved=sum(x['status'] == 'UNRESOLVED_INTERVAL' for x in checks)))
    return dict(leaves=results, certified=sum(x['certified'] for x in results),
        refuted=sum(x['refuted'] for x in results), unresolved=sum(x['unresolved'] for x in results),
        checker_operations=sum(c['ops'] for x in results for c in x['checks']),
        uniform_correlation_proved=False)


def search_task(task):
    id, gamma = task
    start = time.monotonic()
    items = _DISCOVERY[id, gamma]
    rows = {u: SEARCH.leaf_row(x['payload'], x['token_intervals']) for u, x in items.items()}
    meta = _META[id]
    active = [i for i in range(10) if i not in meta['inactive_admissions'][gamma]['indices']]
    target = ['1' if i in active else '0' for i in range(10)]
    rays = SEARCH.ray_dictionary(active)
    K = meta['norm']['certificate']['K']
    witness_cache = {}
    proposals = []
    checker_ops = 0
    for q in SPEC['q']:
        bank = SEARCH.floating_leaf_bank(rows, rays, q)
        rejected = []
        while bank:
            cover = SEARCH.discover_cover(bank, target, K)
            if cover['status'] != 'CONDITIONAL_COVER_PROPOSAL':
                break
            bad = []
            for leaf in cover['leaves']:
                index = leaf['dictionary_index']
                if index not in witness_cache:
                    witness_cache[index] = None
                    for u, item in sorted(items.items()):
                        witness = SEARCH.noncircular_witness(item['payload'], item['token_intervals'], leaf['a'])
                        if witness is not None:
                            admission = require(CHECK.verify_noncircularity(item['payload'], leaf['a'], item['token_intervals'], witness), 'VERIFIED_NONCIRCULARITY')
                            checker_ops += admission['ops']
                            witness_cache[index] = dict(u=u, witness=witness, admission=admission)
                            break
                if witness_cache[index] is None:
                    bad.append(index)
            if not bad:
                break
            rejected.extend(bad)
            bank = [x for x in bank if x['dictionary_index'] not in bad]
        if not bank:
            cover = dict(status='NO_ADMITTED_LOCAL_RAYS', uniform_bound_proved=False)
        if cover['status'] == 'CONDITIONAL_COVER_PROPOSAL':
            for leaf in cover['leaves']:
                calibrated = SEARCH.calibrate_leaf(rows, leaf['a'], q)
                if calibrated is None:
                    raise ArithmeticError('selected finite diagonal does not pay its signed square')
                leaf.update(calibrated, noncircularity=witness_cache[leaf['dictionary_index']], floating_proposal_only=False)
            cover['certificate']['price'] = str(SEARCH.cover_price(cover['leaves'], cover['coefficients'], K))
            cover['admission'] = require(CHECK.verify_cover(target, [x['a'] for x in cover['leaves']], cover['coefficients'], [x['kappa'] for x in cover['leaves']], K, cover['certificate']), 'VERIFIED_CONDITIONAL_COVER')
            checker_ops += cover['admission']['ops']
            exact = checked_leaves(cover, rows, q)
            checker_ops += exact['checker_operations']
            if exact['refuted'] or exact['unresolved']:
                raise ArithmeticError('exact discovery calibration did not certify')
            cover['discovery_checks'] = exact
        cover.update(source_id=id, gamma=gamma, q=q, noncircularity_rejections=rejected,
                     dictionary_rays=len(rays), discovery_parent_count=len(rows))
        proposals.append(cover)
    result = dict(source_id=id, gamma=gamma, proposals=proposals,
        constructor_operations=1000*len(rows)*len(rays)*len(SPEC['q']), checker_operations=checker_ops,
        elapsed_seconds=time.monotonic()-start, worker_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)
    name = 'proposal_'+id+'_gamma_'+gamma.replace('/', '_')+'.json'
    write(OUT/name, result)
    # Full discovery check output remains on disk, not in the multiprocessing queue.
    result['proposals'] = [{k: v for k, v in p.items() if k != 'discovery_checks'} for p in proposals]
    result['file'] = name
    return result


def pool_tasks(function, tasks, initializer, initargs, start, label):
    results, peak, last = [], 0, time.monotonic()
    with mp.get_context('spawn').Pool(SPEC['workers'], initializer=initializer, initargs=initargs) as pool:
        iterator = pool.imap_unordered(function, tasks, chunksize=1)
        while len(results) < len(tasks):
            if time.monotonic()-start > SPEC['module_seconds']:
                raise TimeoutError('079 authorized runtime')
            used = PRIOR.PRIOR.PRIOR.RESOURCES.rss([os.getpid()]+[p.pid for p in pool._pool])
            peak = max(peak, used)
            if used > SPEC['max_aggregate_bytes']:
                raise MemoryError('079 aggregate memory')
            try:
                item = iterator.next(timeout=1)
            except mp.TimeoutError:
                continue
            results.append(item)
            if len(results) == len(tasks) or time.monotonic()-last > 15:
                emit(label, completed=len(results), total=len(tasks)); last = time.monotonic()
    return results, peak


def read_validation(us, id, gamma):
    rows = {}
    for u in us:
        item = json.loads((OUT/('source_'+str(u)+'.json')).read_text())['records'][id][gamma]
        if item['cell_admission']['status'] != 'VERIFIED_CELLS':
            raise ValueError('validation requires admitted physical cells')
        rows[u] = SEARCH.leaf_row(item['payload'], item['token_intervals'])
    return rows


def main():
    if OUT.exists():
        raise FileExistsError('preserve every079 scientific attempt')
    start = time.monotonic()
    counts = validate_parent()
    frozen = {name: (ROOT/name).read_bytes() for name in FILES}
    for name, content in frozen.items():
        if name.endswith('_development.json') and json.loads(content)['status'] != 'PASS':
            raise ValueError('079 development must pass before science')
    discovery, validation = parents(SPEC['discovery_k']), parents(SPEC['validation_k'])
    if set(discovery) & set(validation):
        raise ValueError('fixed discovery/validation parent separation')
    for u in discovery+validation:
        for v in (u, u//2):
            if not (PRIOR.OUT/('source_'+str(v)+'.json')).exists():
                raise ValueError('missing saved078 literal parent source')
    meta = source_metadata()
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for name, content in frozen.items():
        with (OUT/'source_snapshot'/name).open('xb') as f:
            f.write(content)
    try:
        write(OUT/'spec.json', dict(spec=SPEC, prior_frozen_counts=counts, new_frozen_files=len(FILES), discovery_parents=discovery, validation_parents=validation))
        write(OUT/'source_metadata.json', meta)
        data, peak1 = pool_tasks(source_task, [(u, SPEC['gammas']) for u in discovery], initialize_source, (max(discovery)//4,), start, 'flux_discovery_cells')
        proposals, peak2 = pool_tasks(search_task, [(id, gamma) for id in SPEC['source_ids'] for gamma in SPEC['gammas']], initialize_search, (discovery,), start, 'flux_local_cover_proposals')
        candidates = []
        for id in SPEC['source_ids']:
            for q in SPEC['q']:
                options = [dict(p, proposal_file=x['file']) for x in proposals if x['source_id'] == id for p in x['proposals'] if p['q'] == q and p['status'] == 'CONDITIONAL_COVER_PROPOSAL']
                if not options:
                    continue
                best = min(options, key=lambda p: (Q(p['certificate']['price']), len(p['leaves']), Q(p['gamma'])))
                best.update(id=id+'_q'+q.replace('/', '_'), frozen_before_validation=True,
                    source_metadata_file='source_metadata.json', all_uniform_covariance_leaves_unpaid=True,
                    uniform_source_bound_proved=False, RH_proved=False)
                filename = 'candidate_'+best['id']+'.json'
                write(OUT/filename, best)
                candidates.append((best, (OUT/filename).read_bytes()))
        write(OUT/'frozen_candidates.json', dict(candidates=[x for x, _ in candidates], validation_cell_queries_started=False))
        needed = sorted({x['gamma'] for x, _ in candidates}, key=Q)
        validation_data, peak3 = pool_tasks(source_task, [(u, needed) for u in validation], initialize_source, (max(validation)//4,), start, 'flux_validation_cells') if candidates else ([], 0)
        results, checker_ops = [], 0
        for candidate, immutable in candidates:
            rows = read_validation(validation, candidate['source_id'], candidate['gamma'])
            checks = checked_leaves(candidate, rows, candidate['q'])
            checker_ops += checks['checker_operations']
            if (OUT/('candidate_'+candidate['id']+'.json')).read_bytes() != immutable:
                raise ValueError('candidate changed after validation')
            write(OUT/('validation_checks_'+candidate['id']+'.json'), checks)
            failures = [dict(leaf_index=leaf['index'], a=leaf['a'], kappa=leaf['kappa'],
                             first_witness=next(x for x in leaf['checks'] if x['status'] == 'REFUTED_FINITE'),
                             refuted=leaf['refuted']) for leaf in checks['leaves'] if leaf['refuted']]
            result = dict(id=candidate['id'], source_id=candidate['source_id'], q=candidate['q'], gamma=candidate['gamma'],
                leaves=len(candidate['leaves']), conditional_flux_price=candidate['certificate']['price'],
                certified=checks['certified'], refuted=checks['refuted'], unresolved=checks['unresolved'],
                leaf_failures=failures, finite_status='REFUTED_LOCAL_BOUND' if checks['refuted'] else 'UNRESOLVED_INTERVAL' if checks['unresolved'] else 'FINITE_ONLY',
                arithmetic_residual_refuted=False, uniform_correlation_proved=False, RH_proved=False)
            results.append(result)
            emit('flux_cover_validation', id=result['id'], refuted=result['refuted'], leaves=result['leaves'])
        for name, content in frozen.items():
            if (ROOT/name).read_bytes() != content:
                raise ValueError('079 frozen source changed '+name)
        validate_parent()
        all_work = data+proposals+validation_data
        metadata_ops = sum(m['source_binding']['ops']+m['norm_admission']['ops']+m['complete_base']['ops']+sum(x['ops'] for x in m['inactive_admissions'].values()) for m in meta.values())
        report = dict(status='SIGNED_LOCAL_COVARIANCE_SEARCH_COMPLETE', results=results,
            source_programs=len(SPEC['source_ids']), cutoff_exponents=len(SPEC['gammas']),
            cover_proposals=sum(len(x['proposals']) for x in proposals), frozen_candidates=len(candidates),
            discovery_parents=len(discovery), validation_parents=len(validation),
            shared_cell_rows=len(data)*len(SPEC['gammas'])*len(SPEC['source_ids'])+len(validation_data)*len(needed)*len(SPEC['source_ids']),
            constructor_operations=sum(x['constructor_operations'] for x in all_work),
            checker_operations=sum(x['checker_operations'] for x in all_work)+checker_ops+metadata_ops,
            elapsed_seconds=time.monotonic()-start, sampled_parallel_rss_peak_bytes=max(peak1, peak2, peak3),
            conservative_sum_process_peaks_bytes=1024*(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss+SPEC['workers']*max(x['worker_peak_rss_kib'] for x in all_work)),
            prior_frozen_counts=counts, new_frozen_files=len(FILES), hashes_used=False,
            uniform_coefficient_norm_proved=True, complete_R_energy_base_proved=True, uniform_correlation_proved=False,
            uniform_residual_bound_proved=False, uniform_head_bound_proved=False, uniform_core_bound_proved=False,
            new_arithmetic_horizon=False, RH_proved=False)
        write(OUT/'report.json', report)
        write(OUT/'next_search_input.json', dict(schema='local-covariance-bound-feedback-v1', results=results,
            source='D=V(u)-V(floor(u/2)); shared physical integer cells including outer support and cutoff migration',
            paid='fixed-kernel coefficient norm, complete bounded-scale R-energy base, inactive coordinates, exact conditional proper-ray cover',
            unpaid='S_a^2<=kappa*u^(q-1)*Q_a uniformly for each generated local signed covariance leaf',
            failed_leaf_is_not_a_refuted_arithmetic_residual=True,
            next_mechanisms=['joint prime/composite nuisance-mode annihilation', 'parameterized multiplicative cross-moment identities', 'more expressive signed correlation leaves with independently paid prices'],
            do_not_just_increase_kappa=True, original_source_head_core_RH_transfer_still_required=True, RH_proved=False))
        emit('scale_flux_complete', candidates=len(candidates), elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json', dict(type=type(exc).__name__, message=str(exc), RH_proved=False))
        raise


if __name__ == '__main__': main()
