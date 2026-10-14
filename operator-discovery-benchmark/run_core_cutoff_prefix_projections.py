"""Frozen prefix-projection search over preserved independent work samples."""
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
from flint import ctx

import core_cutoff_prefix_projections as P
import run_core_cutoff_prime_orbits as PRIOR
from prime_bank_candidates import Meter

ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_cutoff_prime_orbit_obligation.json'
PUBLIC_INPUT = 'candidate10_cutoff_prefix_projection_obligation.json'
PARENT = ROOT/'core-cutoff-prime-orbit-results/pilot-001'
OUT = ROOT/'core-cutoff-prefix-projection-results/pilot-001'
CAP, WORKER_CAP, SECONDS, MEMORY = 2000000000, 400000000, 1800, 4*1024**3
RECEIPTS = ['core_cutoff_prefix_projections_development.json', 'core_cutoff_prefix_projections_checker_development.json']
FILES = ['core_cutoff_prefix_projections.py', 'check_core_cutoff_prefix_projections.py',
    'run_core_cutoff_prefix_projections.py', 'test_core_cutoff_prefix_projections.py',
    'test_check_core_cutoff_prefix_projections.py', 'core_cutoff_prefix_projections_protocol.txt',
    'CORE_CUTOFF_PRIME_ORBIT_CANDIDATE_REVIEW_026.txt', 'CORE_CUTOFF_PREFIX_PROJECTION_REVIEW_027.txt',
    'prime_bank_candidates.py', INPUT]+RECEIPTS
CACHES = [phase+'_'+role+'_samples.json' for phase in ('discovery', 'evaluation') for role in ('producer', 'checker')]
read, write = PRIOR.read, PRIOR.write


def limit():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, resource.getrlimit(resource.RLIMIT_AS)[1]))


def require_input():
    P.require((ROOT/INPUT).read_bytes() == (PARENT/'publication-001/next_search_input.json').read_bytes(),
              'exact current published full-source input')
    P.require(read(PARENT/'report.json')['status'] == 'FINITE_CUTOFF_PRIME_ORBITS_VERIFIED_WITH_OPEN_SIGNED_CORE',
              'verified preceding finite work study')


def verify():
    PRIOR.verify(); require_input()
    for name in read(OUT/'source_files.json'):
        P.require((ROOT/name).read_bytes() == (OUT/'source_snapshot'/name).read_bytes(), 'unchanged frozen prefix source '+name)
    for name in CACHES:
        P.require((PARENT/name).read_bytes() == (OUT/'cached_samples'/name).read_bytes(), 'unchanged inherited sample bytes '+name)


def cached_samples(role, horizon, meter):
    first = read(OUT/'cached_samples'/('discovery_'+role+'_samples.json'))
    P.require(first['start'] == 2 and first['end'] == 1024, 'complete unit-to-first-stage work cache')
    if horizon == 1024:
        samples = first
    else:
        P.require(horizon == 2048, 'declared cached horizon')
        last = read(OUT/'cached_samples'/('evaluation_'+role+'_samples.json'))
        P.require(last['start'] == 1025 and last['end'] == 2048 and first['mu'] == last['mu'][:1025],
                  'complete inherited continuation and arithmetic prefix')
        samples = dict(first, end=2048, mu=last['mu'], records=first['records']+last['records'], state=last['state'])
    P.require([r['q'] for r in samples['records']] == list(range(2, horizon+1)), 'every cached event once')
    meter.charge(1000*horizon)
    return samples


def worker(role, phase):
    import check_core_cutoff_prefix_projections as C
    limit(); ctx.prec = 192 if role == 'producer' else 256
    meter = Meter(WORKER_CAP, 900); started = time.monotonic()
    engine = P if role == 'producer' else C
    try:
        catalogue = read(OUT/'catalogue.json')
        P.require(catalogue == engine.program_catalogue(), 'independent frozen grammar')
        if phase == 'discovery':
            samples, bases, programs = cached_samples(role, 1024, meter), P.DISCOVERY, catalogue
        else:
            samples, bases = cached_samples(role, 2048, meter), P.EVALUATION
            programs = [catalogue[p['program_id']] for p in read(OUT/'selection.json')['selected']]
        cases = [engine.group_case(program, B, samples, meter) for program in programs for B in bases]
        write(OUT/(phase+'_'+role+'_cases.json'), cases)
        receipt = dict(role=role, phase=phase, operations=meter.operations,
            elapsed_seconds=time.monotonic()-started, cases=len(cases), status='complete',
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, new_source_or_zeta_evaluations=0)
        write(OUT/(phase+'_'+role+'_receipt.json'), receipt)
        print(json.dumps(receipt), flush=True)
    except Exception as error:
        write(OUT/(phase+'_'+role+'_failure.json'), dict(error_type=type(error).__name__, error=str(error),
            operations=meter.operations, elapsed_seconds=time.monotonic()-started, status='incomplete'))
        raise


def run_phase(phase, meter, deadline):
    processes, streams = [], []
    try:
        for role in ('producer', 'checker'):
            stream = (OUT/(phase+'_'+role+'.log')).open('x'); streams.append(stream)
            processes.append((role, subprocess.Popen([sys.executable, '-B', __file__, '--worker', role, phase],
                cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)))
        failed = []
        for role, process in processes:
            code = process.wait(timeout=max(1, min(920, deadline-time.monotonic())))
            if code: failed.append(dict(role=role, returncode=code))
        if failed: raise RuntimeError('preserved projection worker failures '+json.dumps(failed))
        receipts = [read(OUT/(phase+'_'+role+'_receipt.json')) for role in ('producer', 'checker')]
        for r in receipts: meter.charge(r['operations'])
        return receipts
    finally:
        for _, process in processes:
            if process.poll() is None:
                process.terminate()
                try: process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill(); process.wait(timeout=5)
        for stream in streams: stream.close()


def audit_cases(phase, meter):
    import check_core_cutoff_prefix_projections as C
    a, b = [read(OUT/(phase+'_'+role+'_cases.json')) for role in ('producer', 'checker')]
    checked = C.verify_cases(a, b, meter)
    P.require(checked['verified'], 'independent new projection cases')
    write(OUT/(phase+'_verification.json'), checked)
    return a


def main():
    import check_core_cutoff_prefix_projections as C
    import check_core_cutoff_prime_orbits as OLD_CHECK
    from run_core_bound_goal_search import validate_receipts
    started = time.monotonic(); limit(); ctx.prec = 256
    PRIOR.verify(); require_input()
    development = validate_receipts([read(ROOT/name) for name in RECEIPTS])
    OUT.mkdir(parents=True, exist_ok=False)
    meter = Meter(CAP-development, SECONDS)
    try:
        (OUT/'source_snapshot').mkdir(); (OUT/'cached_samples').mkdir()
        for name in FILES: (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
        for name in CACHES: (OUT/'cached_samples'/name).write_bytes((PARENT/name).read_bytes())
        write(OUT/'source_files.json', FILES)
        write(OUT/'protocol.json', dict(schema='cutoff-prefix-projection-run-v1', input=INPUT,
            cached_sources=CACHES, discovery_bases=P.DISCOVERY, evaluation_bases=P.EVALUATION,
            total_operation_cap=CAP, worker_operation_cap=WORKER_CAP, runtime_seconds=SECONDS,
            process_memory_bytes=MEMORY, maximum_concurrent_memory_bytes=3*MEMORY, parallel_workers=2,
            new_source_or_zeta_evaluations=0, numeric_Gram_fitting=False, model_calls_in_search=0,
            fresh_or_unseen_arithmetic_claim=False, hashes=False, whole_signed_bound_proved=False, RH_proved=False))
        meter.charge(2000000)
        parent = read(ROOT/INPUT)
        binding = P.source_binding(parent, meter)
        P.require(binding == C.source_binding(parent, meter), 'independent exact actual-work binding')
        proof = P.proof_search(parent, binding, meter)
        checked = C.verify_proof_search(parent, binding, proof, meter)
        P.require(checked['verified'], 'all generated conditional proof costs and scope')
        write(OUT/'target_binding.json', binding); write(OUT/'proof_search.json', proof)
        write(OUT/'proof_verification.json', checked)
        catalogue = P.program_catalogue()
        P.require(catalogue == C.program_catalogue(), 'independent complete projection generator')
        write(OUT/'catalogue.json', catalogue)
        # Existing independent interval records are replayed, not re-evaluated.
        cached_check = OLD_CHECK.verify_samples(cached_samples('producer', 2048, meter),
                                               cached_samples('checker', 2048, meter), meter)
        P.require(cached_check['verified'], 'complete inherited finite sample evidence')
        write(OUT/'cached_sample_verification.json', cached_check)
        print('Frozen 36 projections and 252 conditional Gram routes; starting parallel cached-work discovery.', flush=True)
        receipts = run_phase('discovery', meter, started+SECONDS)
        discovery = audit_cases('discovery', meter)
        selection = P.select(catalogue, discovery, meter)
        P.require(selection == C.select(catalogue, read(OUT/'discovery_checker_cases.json'), meter),
                  'independent interval-dominance selection')
        write(OUT/'selection.json', selection)
        print('Selection sealed: '+json.dumps(selection['selected'])+'. Evaluating reserved cached block.', flush=True)
        receipts += run_phase('evaluation', meter, started+SECONDS)
        evaluation = audit_cases('evaluation', meter)
        cases = discovery+evaluation; artifact = str(OUT.relative_to(ROOT))
        output = P.feedback(parent, binding, proof, selection, cases, artifact)
        checked_feedback = C.verify_feedback(parent, binding, proof, selection, cases, output, artifact, meter)
        P.require(checked_feedback['verified'], 'complete source, original alternatives and new open Gram tasks')
        write(OUT/'feedback_verification.json', checked_feedback); write(OUT/'next_search_input.json', output)
        verify()
        report = dict(status='PREFIX_PROJECTIONS_AND_CONDITIONAL_GRAM_ROUTES_VERIFIED_WITH_OPEN_SIGNED_CORE',
            **proof['statistics'], discovery_cases=len(discovery), evaluation_cases=len(evaluation),
            selected=selection['selected'], rejected=selection['rejected'], undominated_by_lane=selection['undominated_by_lane'],
            evaluation=[{k:c[k] for k in ('program_id', 'B', 'grouped_peak_absolute', 'ungrouped_absolute',
                'joined_total', 'odd_total', 'even_total', 'cross_scale_groups', 'groups_with_opposite_mu',
                'prime_composite_groups', 'cancellation_bits')} for c in evaluation],
            inherited_source_bindings=len(parent['generated_bound_obligations']),
            new_source_or_zeta_evaluations=0, numeric_Gram_fitting=False, model_calls_in_search=0,
            development_operations=development, study_operations=meter.operations,
            inclusive_operations=development+meter.operations, elapsed_seconds=time.monotonic()-started,
            main_peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss, worker_receipts=receipts,
            full_component_bound_proved=False, whole_signed_bound_proved=False, RH_proved=False)
        write(OUT/'report.json', report)
        publication = OUT/'publication-001'; publication.mkdir()
        raw = (OUT/'next_search_input.json').read_bytes()
        for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
            with path.open('xb') as stream: stream.write(raw)
        write(OUT.parent/'latest.json', dict(input=PUBLIC_INPUT, status=report['status'],
            report=str((OUT/'report.json').relative_to(ROOT)), whole_signed_bound_proved=False, RH_proved=False))
        print(json.dumps(report), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(error_type=type(error).__name__, error=str(error),
            operations=meter.operations, development_operations=development, status='incomplete',
            whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    if len(sys.argv) == 4 and sys.argv[1] == '--worker' and sys.argv[2] in ('producer', 'checker') and sys.argv[3] in ('discovery', 'evaluation'):
        worker(sys.argv[2], sys.argv[3])
    elif len(sys.argv) == 1: main()
    else: raise SystemExit('invalid invocation')
