"""Freeze, parallelize, independently audit, and publish the orbit search."""
import json
from pathlib import Path
import resource
import subprocess
import sys
import time

from flint import arb, ctx
import core_cutoff_prime_orbits as P
import run_core_cutoff_work_search as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_cutoff_work_obligation.json'
PUBLIC_INPUT = 'candidate10_cutoff_prime_orbit_obligation.json'
PARENT = ROOT/'core-cutoff-work-results/pilot-001'
OUT = ROOT/'core-cutoff-prime-orbit-results/pilot-001'
CAP, WORKER_CAP, SECONDS, MEMORY = 1500000000, 300000000, 1800, 4*1024**3
RECEIPTS = ['core_cutoff_prime_orbits_development.json', 'core_cutoff_prime_orbits_checker_development.json']
FILES = ['core_cutoff_prime_orbits.py', 'check_core_cutoff_prime_orbits.py',
    'run_core_cutoff_prime_orbits.py', 'test_core_cutoff_prime_orbits.py',
    'test_check_core_cutoff_prime_orbits.py', 'core_cutoff_prime_orbits_protocol.txt',
    'CORE_CUTOFF_PRIME_ORBIT_REVIEW_025.txt', 'prime_bank_candidates.py',
    'run_core_cutoff_frame.py', INPUT]+RECEIPTS
read, write = PRIOR.read, PRIOR.write


def limit():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))


def require_input():
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('exact preceding complete source obligation required')
    if read(PARENT/'report.json')['status'] != 'CUTOFF_BOUND_COMPOSITIONS_VERIFIED_WITH_OPEN_SIGNED_CORE':
        raise ValueError('verified preceding signed-work composition required')


def verify():
    PRIOR.verify()
    require_input()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen prime-orbit source '+name)


def worker(role, phase):
    import check_core_cutoff_prime_orbits as C
    from run_core_cutoff_frame import archived_mu
    limit()
    ctx.prec = 192 if role == 'producer' else 256
    engine = P if role == 'producer' else C
    meter = Meter(WORKER_CAP, 900)
    started = time.monotonic()
    stem = OUT/(phase+'_'+role)
    try:
        catalogue = read(OUT/'catalogue.json')
        P.require(catalogue == engine.program_catalogue(), 'independent sealed catalogue')
        if phase == 'discovery':
            start, end, previous, bases, programs = 2, 1024, None, P.DISCOVERY, catalogue
        else:
            start, end = 1025, 2048
            previous = read(OUT/('discovery_'+role+'_samples.json'))['state']
            bases = P.EVALUATION
            selected = read(OUT/'selection.json')['selected']
            programs = [catalogue[x['program_id']] for x in selected]
        mu = archived_mu(role, end, meter)
        samples = engine.measure(mu, start, end, previous, meter)
        write(Path(str(stem)+'_samples.json'), samples)
        cases = [engine.group_case(program, B, samples, meter) for program in programs for B in bases]
        write(Path(str(stem)+'_cases.json'), cases)
        receipt = dict(role=role, phase=phase, operations=meter.operations,
            elapsed_seconds=time.monotonic()-started, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            records=len(samples['records']), cases=len(cases), status='complete')
        write(Path(str(stem)+'_receipt.json'), receipt)
        print(json.dumps(receipt), flush=True)
    except Exception as error:
        write(Path(str(stem)+'_failure.json'), dict(error_type=type(error).__name__, error=str(error),
            operations=meter.operations, elapsed_seconds=time.monotonic()-started, status='incomplete'))
        raise


def phase_run(phase, meter, deadline):
    processes, streams = [], []
    try:
        for role in ('producer', 'checker'):
            stream = (OUT/(phase+'_'+role+'.log')).open('x')
            streams.append(stream)
            processes.append((role, subprocess.Popen([sys.executable, '-B', __file__, '--worker', role, phase],
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)))
        failures = []
        for role, process in processes:
            code = process.wait(timeout=max(1, min(920, deadline-time.monotonic())))
            if code:
                failures.append(dict(role=role, returncode=code))
        if failures:
            raise RuntimeError('preserved numeric worker failure: '+json.dumps(failures))
        receipts = [read(OUT/(phase+'_'+role+'_receipt.json')) for role in ('producer', 'checker')]
        for receipt in receipts:
            meter.charge(receipt['operations'])
        return receipts
    finally:
        for _, process in processes:
            if process.poll() is None:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill(); process.wait(timeout=5)
        for stream in streams:
            stream.close()


def audit_phase(phase, meter):
    import check_core_cutoff_prime_orbits as C
    producer = read(OUT/(phase+'_producer_samples.json'))
    checker = read(OUT/(phase+'_checker_samples.json'))
    samples = C.verify_samples(producer, checker, meter)
    cases = read(OUT/(phase+'_producer_cases.json'))
    independent = read(OUT/(phase+'_checker_cases.json'))
    case_check = C.verify_cases(cases, independent, meter)
    P.require(samples['verified'] and case_check['verified'], 'independent complete finite evidence audit')
    result = dict(samples=samples, cases=case_check)
    write(OUT/(phase+'_verification.json'), result)
    return cases


def main():
    import check_core_cutoff_prime_orbits as C
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic()
    limit()
    ctx.prec = 256
    PRIOR.verify()
    require_input()
    development = validate_receipts([read(ROOT/name) for name in RECEIPTS])
    OUT.mkdir(parents=True, exist_ok=False)
    meter = Meter(CAP-development, SECONDS)
    try:
        (OUT/'source_snapshot').mkdir()
        for name in FILES:
            (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='core-cutoff-prime-orbit-run-v1', input=INPUT,
            discovery_bases=P.DISCOVERY, evaluation_bases=P.EVALUATION, heights=P.HEIGHTS,
            precision=dict(producer=192, checker=256), total_operation_cap=CAP, worker_operation_cap=WORKER_CAP,
            total_runtime_limit_seconds=SECONDS, worker_runtime_limit_seconds=900,
            per_process_memory_limit_bytes=MEMORY, concurrent_numeric_workers=2,
            maximum_concurrent_memory_limit_bytes=3*MEMORY, model_calls_in_search=0, fitted_constants=0,
            hashes=False, continuous_integral_control=False, fresh_arithmetic_holdout=False,
            testing='recorded owned development suites; independent actual evidence audit',
            whole_signed_bound_proved=False, RH_proved=False))
        parent = read(ROOT/INPUT)
        binding = P.bind_target(parent, meter)
        P.require(binding == C.bind_target(parent, meter), 'independently bound current polynomial and source')
        write(OUT/'target_binding.json', binding)
        catalogue = P.program_catalogue()
        P.require(catalogue == C.program_catalogue(), 'independent complete grammar')
        write(OUT/'catalogue.json', catalogue)
        meter.charge(2000000)
        print('Frozen grammar and exact target; starting parallel discovery measurements.', flush=True)
        discovery_receipts = phase_run('discovery', meter, started+SECONDS)
        discovery = audit_phase('discovery', meter)
        selection = P.select(catalogue, discovery)
        independent_selection = C.select(catalogue, read(OUT/'discovery_checker_cases.json'))
        P.require(selection == independent_selection, 'independent selection including exclusions and tie rule')
        write(OUT/'selection.json', selection)
        print('Selection sealed: '+json.dumps(selection['selected'])+'. Extending each saved state once.', flush=True)
        evaluation_receipts = phase_run('evaluation', meter, started+SECONDS)
        evaluation = audit_phase('evaluation', meter)
        # Phase2 begins at its own saved state; additionally audit the public
        # boundary and source prefix between the two independently checked phases.
        for role in ('producer', 'checker'):
            earlier = read(OUT/('discovery_'+role+'_samples.json'))
            later = read(OUT/('evaluation_'+role+'_samples.json'))
            P.require(earlier['end']+1 == later['start'] and later['mu'][:earlier['end']+1] == earlier['mu']
                and len(earlier['state']['last_energy']) == len(later['initial_energy']) == len(P.HEIGHTS)
                and all(arb(a).overlaps(arb(b)) for a, b in
                    zip(earlier['state']['last_energy'], later['initial_energy'])),
                'one complete continuation without restart')
        all_cases = discovery+evaluation
        artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, binding, selection, all_cases, artifact)
        checked = C.verify_feedback(parent, binding, selection, all_cases, output, artifact, meter)
        P.require(checked['verified'], 'complete inherited source and open-bound feedback')
        write(OUT/'feedback_verification.json', checked)
        write(OUT/'next_search_input.json', output)
        verify()
        report = dict(status='FINITE_CUTOFF_PRIME_ORBITS_VERIFIED_WITH_OPEN_SIGNED_CORE',
            grammar_programs=len(catalogue), discovery_cases=len(discovery), evaluation_cases=len(evaluation),
            selected=selection['selected'], rejected=selection['rejected'],
            evaluation=[{k: c[k] for k in ('program_id', 'B', 'cancellation_bits', 'nontrivial_partition',
                'grouped_peak_absolute', 'ungrouped_absolute', 'joined_total', 'odd_total', 'even_total',
                'singleton_absolute')} for c in evaluation],
            sampled_integer_events_per_owner=2047, sampled_heights=len(P.HEIGHTS),
            original_source_bindings_retained=len(parent['generated_bound_obligations']),
            worker_receipts=discovery_receipts+evaluation_receipts,
            development_operations=development, study_operations=meter.operations,
            inclusive_operations=development+meter.operations,
            elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            model_calls_in_search=0, fitted_constants=0, continuous_integral_control=False,
            source_history='previously observed Mobius coefficients; new sampled cutoff-work observables',
            new_uniform_signed_arithmetic_estimates=0, new_component_bounds_proved=0,
            whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'; publication.mkdir()
        raw = (OUT/'next_search_input.json').read_bytes()
        for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
            with path.open('xb') as stream:
                stream.write(raw)
        write(OUT.parent/'latest.json', dict(report=str((OUT/'report.json').relative_to(ROOT)),
            input=PUBLIC_INPUT, status=report['status'], whole_signed_bound_proved=False, RH_proved=False))
        print(json.dumps(report), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(error_type=type(error).__name__, error=str(error),
            operations=meter.operations, development_operations=development, status='incomplete',
            whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    if len(sys.argv) == 4 and sys.argv[1] == '--worker' and sys.argv[2] in ('producer', 'checker') and sys.argv[3] in ('discovery', 'evaluation'):
        worker(sys.argv[2], sys.argv[3])
    elif len(sys.argv) == 1:
        main()
    else:
        raise SystemExit('invalid invocation')
