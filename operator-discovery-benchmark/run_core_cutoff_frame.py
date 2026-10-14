"""Immutable two-phase search for signed recovery across exact cutoffs.

Actual numerical observables are recovery costs, not residual energy bounds.
New proof obligations retain both costs and the full joined residual.
"""
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as Q
import gzip
import json
import multiprocessing as mp
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from flint import arb, ctx
from prime_bank_candidates import Meter
import core_cutoff_frame as P
import check_core_cutoff_frame as C
import core_joint_power_search as JOINT
import check_core_joint_power_search as JOINT_CHECK
import check_core_prefix_proof_search as PREFIX_CHECK
import run_core_joint_power_search as PRIOR

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'core-cutoff-frame-results/pilot-001'
PARENT = ROOT/'core-joint-power-results/pilot-001'
PREFIX = ROOT/'core-prefix-proof-results/pilot-001'
SOURCE = ROOT/'core-signed-work-results/pilot-001'
INPUT = 'candidate10_joint_power_obligation.json'
DISCOVERY = [2**k for k in range(14)]
EVALUATION = [2**k for k in range(14, 18)]
TESTS = ['test_core_cutoff_frame', 'test_check_core_cutoff_frame', 'test_run_core_cutoff_frame']
RECEIPTS = ['core_cutoff_frame_development.json', 'core_cutoff_frame_checker_development.json',
            'core_cutoff_frame_runner_development.json']
FILES = ['core_cutoff_frame.py', 'check_core_cutoff_frame.py', 'run_core_cutoff_frame.py',
         'core_cutoff_frame_protocol.txt', 'prime_bank_candidates.py', INPUT]+[t+'.py' for t in TESTS]+RECEIPTS
MAIN_CAP, WORKER_CAP, TOTAL_CAP = 200000000, 600000000, 1500000000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write('\n')


def limits():
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))


def tight(value):
    return value.is_finite() and value.rad() <= arb(2)**-96*(1+abs(value.mid()))


def serial(value):
    if isinstance(value, arb):
        if not value.is_finite():
            raise ArithmeticError('nonfinite observable')
        # Keep the complete enclosure; a wide interval is an unresolved result.
        return value.str(85)
    if isinstance(value, dict):
        return {k: serial(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [serial(v) for v in value]
    return value


def verify():
    PRIOR.verify()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    for item in read(OUT/'parent_proof_files.json'):
        if (ROOT/item['original']).read_bytes() != (OUT/'parent_proof_snapshot'/item['copy']).read_bytes():
            raise ValueError('changed inherited proof artifact '+item['original'])


def authenticated_representations(prior, meter):
    prefix_input = prior['parent_obligation']
    inverse_input = prefix_input['parent_obligation']
    bound_input = inverse_input['parent_obligation']
    rows = inverse_input['source_geometries']
    constructions = {o['id']: o['construction'] for o in bound_input['generated_bound_program_obligations']}
    prefix_parents = {(p['geometry_id'], p['parent_obligation_id']): p for p in prefix_input['generated_prefix_bound_obligations']}
    inverse_parents = {(p['source_geometry_ref'], p['parent_obligation_id']): p for p in inverse_input['generated_joined_obligations']}
    expected = {(r['id'], ident) for r in rows for ident in constructions}
    if set(prefix_parents) != expected or set(inverse_parents) != expected:
        raise ValueError('complete inherited channel and source bindings')
    geometry_data, proof_checks = [], []
    for row in rows:
        prefix = read(OUT/'parent_proof_snapshot'/('prefix-geometry-'+str(row['id'])+'.json'))
        joint = read(OUT/'parent_proof_snapshot'/('joint-geometry-'+str(row['id'])+'.json'))
        PREFIX_CHECK._source_terms(row, meter)
        checks = JOINT_CHECK.verify_search(row, prefix, joint['remaining_refs'], joint, meter)
        complete = joint['alternatives'][(1 << len(joint['eligible']))-1]
        if complete['unchanged_ids'] or len(complete['joint_drifts']) != 1:
            raise ValueError('complete finite-head centering and one common drift profile')
        view = dict(joint, selected_mask=complete['mask'])
        bindings = []
        for ident, construction in constructions.items():
            parent = prefix_parents[(row['id'], ident)]
            full_reduction = JOINT.reduction(parent, construction, view)
            JOINT_CHECK.verify_reduction(parent, construction, view, full_reduction, meter)
            old = inverse_parents[(row['id'], ident)]['paid_component_reduction']
            group_constants = [old['combined_paid_coarse_constant'], parent['combined_new_paid_constant'], full_reduction['combined_paid_constant']]
            nonzero = [Q(v) for v in group_constants if Q(v)]
            if any(c < 0 for c in nonzero):
                raise ValueError('nonnegative uniform paid costs')
            paid_constant = len(nonzero)*sum(nonzero, Q(0))
            bindings.append(dict(parent_obligation_id=ident, inherited_target_p=parent['goal']['p'],
                paid_groups=dict(short_inverse=old['paid_components'], prefix=parent['newly_paid'],
                                 complete_power=full_reduction['newly_paid']),
                paid_group_constants=group_constants, paid_cauchy_count=len(nonzero),
                combined_all_paid_constant=str(paid_constant),
                remaining_source_refs=full_reduction['remaining_source_refs'],
                remaining_centered_remainders=full_reduction['remaining_centered_remainders'],
                exact_transport_error='-e with e=f-g from the inherited transport',
                all_remaining_crosses_retained=True, complete_reduction=full_reduction))
        drift = complete['joint_drifts'][0]
        geometry_data.append(dict(geometry_id=row['id'], alpha=row['alpha'], gamma=row['gamma'],
            complete_mask=complete['mask'], prior_selected_mask=joint['selected_mask'],
            drift=drift, all_finite_head_remainders_paid=all(r['energy']['uniform_constant'] is not None for r in complete['remainders']),
            bindings=bindings))
        proof_checks.append(checks)
    if len({(g['drift']['theta'], json.dumps(g['drift']['polynomial'], sort_keys=True)) for g in geometry_data}) != 1:
        raise ValueError('cutoff-only aliasing requires one exact common drift polynomial')
    write(OUT/'source_representation_checks.json', dict(checks=proof_checks,
        binding_count=sum(len(g['bindings']) for g in geometry_data),
        old_selected_alternatives_unchanged=True, full_alternatives_independently_checked=True,
        recovery='g=P_i+R_i+d_i*J for every geometry i at COMMON N=4X-1',
        paid_group_rule='C_Pi=r_i*sum(C_group), counting every nonzero group',
        whole_signed_bound_proved=False))
    return geometry_data, list(constructions)


def archived_mu(role, H, meter):
    mu = None
    with gzip.open(SOURCE/(role+'_vectors.jsonl.gz'), 'rt') as f:
        for line in f:
            row = json.loads(line)
            meter.charge(3*len(row['values']))
            if row['name'] == 'mode:mu':
                if len(row['values']) < H+1:
                    raise ValueError('complete archived source prefix')
                mu = []
                for text in row['values'][:H+1]:
                    value = arb(text)
                    integers = [k for k in (-1, 0, 1) if value == arb(k)]
                    if len(integers) != 1:
                        raise ArithmeticError('archived mu must be an exact integer')
                    mu.append(integers[0])
                    meter.charge(10)
                break
    if mu is None:
        raise ValueError('missing independently certified mu archive')
    return mu


def worker(role, phase, candidate_ids, cap):
    limits()
    start = time.monotonic()
    meter = Meter(cap, 1800)
    ctx.prec = 192 if role == 'producer' else 224
    engine = P if role == 'producer' else C
    catalogue = read(OUT/'catalogue.json')
    geometries = read(OUT/'representations.json')
    scales = DISCOVERY if phase == 'discovery' else EVALUATION
    requests = {'a': set(), 'b': set()}
    cutoffs = {}
    for X in scales:
        cutoffs[X] = [(P.cutoff(4*X-1, g['alpha']), P.cutoff(4*X-1, g['gamma'])) for g in geometries]
        for U, V in cutoffs[X]:
            requests['a'].add(U)
            requests['b'].add(V)
        for (U, V), g in zip(cutoffs[X], geometries):
            for value, key in [(U, 'alpha'), (V, 'gamma')]:
                r = Q(g[key])
                if not value**r.denominator <= (4*X-1)**r.numerator < (value+1)**r.denominator:
                    raise ArithmeticError('exact integer rational cutoff certificate')
    requests = {name: sorted(v) for name, v in requests.items()}
    mu = archived_mu(role, max(max(v) for v in requests.values()), meter)
    values = engine.moments(mu, requests, meter)
    z = (arb(2)/3).zeta()
    Ru = (arb(9)/2)*((arb(4)/3).zeta()/(z*z)-1/z)
    scalar = read(OUT/'parent_proof_snapshot/source_scalar.json')
    if not Ru.overlaps(arb(scalar['R_u'])) or not abs(Ru) < 5:
        raise ArithmeticError('complete actual source scalar at own precision')
    meter.charge(10000)
    observations = []
    for X in scales:
        drifts, aliases = [], []
        for (U, V), g in zip(cutoffs[X], geometries):
            aliases.append([values['effective_cutoffs'][str(U)], values['effective_cutoffs'][str(V)]])
            drifts.append(engine.drift(g['drift']['polynomial'], values['a'][str(U)], values['b'][str(V)], Ru, meter))
        candidates = []
        for ident in candidate_ids:
            value = engine.evaluate(catalogue['candidates'][ident], catalogue['basis'], drifts, aliases, meter)
            candidates.append(dict(id=ident, **value))
        observations.append(dict(X=X, N=4*X-1, cutoffs=cutoffs[X], aliases=aliases, drifts=drifts, candidates=candidates))
    output = dict(role=role, phase=phase, precision_bits=ctx.prec, requests=requests, moments=values,
        R_u=Ru, observations=observations, operations=meter.operations, elapsed_seconds=time.monotonic()-start,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        moment_method='direct cube roots' if role == 'producer' else 'Abel from exact Mertens prefixes with log-exp powers',
        frame_method='factorized square pooling' if role == 'producer' else 'independent expanded polynomials',
        actual_source_regenerated=False, uniform_signed_bound_proved=False)
    path = OUT/(phase+'-'+role+'.json')
    write(path, serial(output))
    return dict(role=role, phase=phase, path=path.name, operations=meter.operations, elapsed_seconds=time.monotonic()-start)


def run_phase(phase, candidate_ids, used):
    results = []
    with ProcessPoolExecutor(max_workers=2, mp_context=mp.get_context('spawn')) as pool:
        futures = {pool.submit(worker, role, phase, candidate_ids, WORKER_CAP-used.get(role, 0)): role for role in ('producer', 'checker')}
        failures = []
        for future in as_completed(futures):
            role = futures[future]
            try:
                result = future.result()
                results.append(result)
                print(json.dumps(result), flush=True)
            except Exception as error:
                failure = dict(role=role, phase=phase, error_type=type(error).__name__, error=str(error))
                write(OUT/(phase+'-'+role+'-failure.json'), failure)
                failures.append(failure)
        if failures:
            raise RuntimeError('worker terminal failure; preserve completed outputs')
    return results


def compare(phase, meter):
    left, right = [read(OUT/(phase+'-'+role+'.json')) for role in ('producer', 'checker')]
    comparisons = 0

    def overlap(a, b):
        nonlocal comparisons
        comparisons += 1
        meter.charge(20)
        a, b = arb(a), arb(b)
        if not a.is_finite() or not b.is_finite() or not a.overlaps(b):
            raise ArithmeticError('independent enclosure disagreement')
        return tight(a) and tight(b)

    if left['requests'] != right['requests'] or left['moments']['effective_cutoffs'] != right['moments']['effective_cutoffs']:
        raise ValueError('same exact cutoffs and source support')
    all_moments_tight = overlap(left['R_u'], right['R_u'])
    for name in ('a', 'b'):
        if set(left['moments'][name]) != set(right['moments'][name]):
            raise ValueError('complete moment comparison')
        for key in left['moments'][name]:
            all_moments_tight &= overlap(left['moments'][name][key], right['moments'][name][key])
    combined = []
    if len(left['observations']) != len(right['observations']):
        raise ValueError('complete observation comparison')
    for a, b in zip(left['observations'], right['observations']):
        if any(a[key] != b[key] for key in ('X', 'N', 'cutoffs', 'aliases')):
            raise ValueError('same whole source horizon and exact alias groups')
        reliable = all_moments_tight
        for x, y in zip(a['drifts'], b['drifts']):
            reliable &= overlap(x, y)
        if [c['id'] for c in a['candidates']] != [c['id'] for c in b['candidates']]:
            raise ValueError('same complete candidate evaluations')
        candidates = []
        for ca, cb in zip(a['candidates'], b['candidates']):
            good = overlap(ca['normalizer'], cb['normalizer']) and reliable
            for x, y in zip(ca['weights'], cb['weights']):
                good &= overlap(x, y)
            if ca['status'] == 'exact_singular' or cb['status'] == 'exact_singular':
                if ca['status'] != cb['status']:
                    raise ArithmeticError('exact singularity must independently agree')
                status = 'exact_singular'
            elif ca['K'] is None or cb['K'] is None:
                status = 'unresolved_positive'
            else:
                good &= overlap(ca['K'], cb['K'])
                for x, y in zip(ca['lambda'], cb['lambda']):
                    good &= overlap(x, y)
                status = 'certified_positive' if good else 'unresolved_wide'
            candidates.append(dict(id=ca['id'], status=status, K=cb['K'], normalizer=cb['normalizer']))
        combined.append(dict(X=a['X'], candidates=candidates))
    result = dict(phase=phase, verified=True, comparisons=comparisons, observations=combined,
        all_moments_tight=all_moments_tight, fresh_source_holdout=False,
        complete_signed_residual_evaluated=False, whole_signed_bound_proved=False)
    write(OUT/(phase+'-comparison.json'), result)
    return result


def select(catalogue, observations, geometries, meter):
    by_id = {c['id']: [] for c in catalogue['candidates']}
    for observation in observations:
        for c in observation['candidates']:
            by_id[c['id']].append(dict(X=observation['X'], **c))
    rankings = []
    for item in catalogue['candidates']:
        values = by_id[item['id']]
        failed = [dict(X=v['X'], status=v['status']) for v in values if v['status'] != 'certified_positive']
        exponent = None
        if not failed:
            exponents = [(arb(b['K'])/arb(a['K'])).log()/arb(2).log() for a, b in zip(values, values[1:])]
            exponent = max(float(e.upper()) for e in exponents)
        rankings.append(dict(id=item['id'], support_size=len(item['active_coordinates']),
            basis_count=len(item['basis_ids']), worst_observed_doubling_exponent=exponent,
            finite_nonsingular=not failed, failures=failed))
        meter.charge(200)
    selected = []
    for size in range(2, len(geometries)+1):
        eligible = [r for r in rankings if r['support_size'] == size and r['finite_nonsingular']]
        if eligible:
            winner = min(eligible, key=lambda r: (r['worst_observed_doubling_exponent'], r['basis_count'], r['id']))
            selected.append(dict(id=winner['id'], route='recovery_conditioning_support_'+str(size)))
    paid = [i for i, g in enumerate(geometries) if g['all_finite_head_remainders_paid']]
    only_paid = [c for c in catalogue['candidates'] if c['active_coordinates'] == paid]
    if len(paid) != 2 or len(only_paid) != 1:
        raise ValueError('protocol reserves exactly the pair of fully paid head representations')
    selected.append(dict(id=only_paid[0]['id'], route='all_centered_finite_heads_paid'))
    return dict(schema='cutoff-frame-selection-v1', rankings=rankings, selected=selected,
        selected_ids=sorted({v['id'] for v in selected}), discovery_scales=DISCOVERY,
        evaluation_read=False, selection_scope='recovery conditioning only; signed residual bound remains open',
        constants_fitted=False, model_calls=0, whole_signed_bound_proved=False)


def main():
    limits()
    start = time.monotonic()
    ctx.prec = 224
    PRIOR.verify()
    if read(PARENT/'report.json')['status'] != 'JOINT_POWER_CONTROLS_VERIFIED_WITH_OPEN_SIGNED_DRIFT':
        raise ValueError('verified prior complete joint power proof stage')
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('exact current published obligation')
    prior = read(ROOT/INPUT)
    if prior['whole_signed_bound_proved'] or prior['RH_proved']:
        raise ValueError('open signed arithmetic target')
    receipts = [read(ROOT/p) for p in RECEIPTS]
    if any(r['runs'][-1]['returncode'] or r['operations'] != sum(v['operations'] for v in r['runs']) for r in receipts):
        raise ValueError('passed owned development suites')
    if OUT.exists():
        raise FileExistsError('preserve one immutable study, including failed outcomes')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    (OUT/'parent_proof_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    geometries = prior['parent_obligation']['parent_obligation']['source_geometries']
    proof_files = []
    for g in geometries:
        for prefix, directory in [('joint', PARENT), ('prefix', PREFIX)]:
            name = 'geometry-'+str(g['id'])+'.json'
            proof_files.append(dict(original=str((directory/name).relative_to(ROOT)), copy=prefix+'-'+name))
    proof_files.append(dict(original=str((PARENT/'source_scalar.json').relative_to(ROOT)), copy='source_scalar.json'))
    # The joint stage retains its scalar in the parent snapshot.
    proof_files[-1]['original'] = str((PARENT/'parent_proof_snapshot/source_scalar.json').relative_to(ROOT))
    for item in proof_files:
        (OUT/'parent_proof_snapshot'/item['copy']).write_bytes((ROOT/item['original']).read_bytes())
    write(OUT/'parent_proof_files.json', proof_files)
    write(OUT/'protocol.json', dict(schema='core-cutoff-frame-run-v1', input=INPUT,
        grammar='generic degree1 polynomial kernel; exhaustive nonempty square-pool subsets',
        discovery_scales=DISCOVERY, evaluation_scales=EVALUATION, common_horizon='N=4X-1',
        selection='worst finite recovery doubling exponent, then basis count, then id; separate support sizes; retain fully paid head pair',
        supplied=['language and resource bounds', 'linear and Cauchy recovery', 'moment semantics', 'selection policy'],
        generated=['generic nullspace', 'all signed eliminators', 'recovery denominator', 'selected construction', 'remaining proof obligations'],
        analyst_nominated_frame_coefficients=False, model_calls_in_search=0, hashes=False,
        new_source_coefficients=False, fresh_source_holdout=False, signed_residual_energy_evaluated=False,
        worker_precision_bits=[192, 224], phase_worker_cap_seconds=1800, main_cap_seconds=3600,
        role_operation_cap=WORKER_CAP, main_operation_cap=MAIN_CAP, inclusive_operation_cap=TOTAL_CAP,
        per_process_memory_bytes=4*1024**3, total_memory_ceiling_bytes=16*1024**3,
        whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(MAIN_CAP, 3600)
    meter.charge(2000000)
    tests_start = time.monotonic()
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT, capture_output=True, text=True, timeout=300)
    test_ops = sum(map(int, re.findall(r'operations=(\d+)', tests.stdout)))
    write(OUT/'frozen_tests.json', dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr,
        operations=test_ops, elapsed_seconds=time.monotonic()-tests_start))
    if tests.returncode:
        raise RuntimeError('frozen owned test suites failed')
    ctx.prec = 224
    catalogue = P.catalogue(len(geometries), meter)
    proof = C.check_catalogue(catalogue, meter)
    write(OUT/'catalogue.json', catalogue)
    write(OUT/'catalogue_verification.json', proof)
    representations, bindings = authenticated_representations(prior, meter)
    write(OUT/'representations.json', representations)
    print(json.dumps(dict(stage='structure_frozen_before_moments', basis=len(catalogue['basis']),
        candidates=len(catalogue['candidates']), verified=proof['verified'], operations=meter.operations)), flush=True)
    discovery_workers = run_phase('discovery', [c['id'] for c in catalogue['candidates']], {})
    discovery = compare('discovery', meter)
    selection = select(catalogue, discovery['observations'], representations, meter)
    write(OUT/'selection.json', selection)
    print(json.dumps(dict(stage='selection_frozen_before_evaluation', selected=selection['selected'],
        finite_nonsingular=sum(r['finite_nonsingular'] for r in selection['rankings']))), flush=True)
    used = {r['role']: r['operations'] for r in discovery_workers}
    evaluation_workers = run_phase('evaluation', selection['selected_ids'], used)
    evaluation = compare('evaluation', meter)
    obligations, evaluation_summary = [], []
    for ident in selection['selected_ids']:
        observed = [next(c for c in x['candidates'] if c['id'] == ident) for x in evaluation['observations']]
        all_positive = all(c['status'] == 'certified_positive' for c in observed)
        state = 'finite_recovery_observed' if all_positive else 'finite_recovery_not_established_at_every_evaluation_scale'
        obligations.append(P.feedback(catalogue['candidates'][ident], bindings, state))
        evaluation_summary.append(dict(id=ident, status=state, observations=[dict(X=X, **c) for X, c in zip(EVALUATION, observed)],
            uniform_recovery_proved=False, signed_residual_bound_proved=False))
    next_input = dict(schema='core-cutoff-frame-feedback-v1', status='open', parent_obligation=prior,
        catalogue_file='core-cutoff-frame-results/pilot-001/catalogue.json',
        source_representations_file='core-cutoff-frame-results/pilot-001/representations.json',
        generated_bound_constructions=obligations, evaluation_summary=evaluation_summary,
        next_priority='Search arithmetic controls for generated recovery denominators AND complete weighted residual energy; positive finite denominators alone cannot pay the signed core',
        unsolved_estimates_are_explicit_search_inputs=True, detector_has_general_analytic_prover=False,
        supplied_versus_generated_recorded=True, original_target_and_all_corrections_retained=True,
        no_original_fixed_recurrence_discharged=True, all_scale_signed_control_proved=False,
        whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'next_search_input.json', next_input)
    total = meter.operations+sum(r['operations'] for r in discovery_workers+evaluation_workers)+test_ops+sum(r['operations'] for r in receipts)
    if total > TOTAL_CAP:
        raise OverflowError('inclusive operation cap')
    verify()
    report = dict(status='CUTOFF_FRAME_CONSTRUCTIONS_VERIFIED_WITH_OPEN_ARITHMETIC_BOUNDS',
        geometries=len(representations), source_bindings=len(representations)*len(bindings),
        generic_kernel_rank=catalogue['constraint_rank'], basis_vectors=len(catalogue['basis']),
        generated_candidates=len(catalogue['candidates']), selected=selection['selected'],
        discovery_finite_nonsingular=sum(r['finite_nonsingular'] for r in selection['rankings']),
        finite_evaluation_passes=sum(r['status'] == 'finite_recovery_observed' for r in evaluation_summary),
        comparison_count=discovery['comparisons']+evaluation['comparisons'],
        evaluation_summary=evaluation_summary, main_operations=meter.operations, inclusive_operations=total,
        worker_receipts=discovery_workers+evaluation_workers, elapsed_seconds=time.monotonic()-start,
        peak_main_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        source_regenerated=False, new_moment_observables=True, fresh_source_holdout=False,
        full_signed_residual_evaluated=False, uniform_recovery_proved=False,
        whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'report.json', report)
    print(json.dumps({k: v for k, v in report.items() if k != 'evaluation_summary'}), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'report.json').exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__,
                error=str(error), whole_signed_bound_proved=False, RH_proved=False))
        raise
