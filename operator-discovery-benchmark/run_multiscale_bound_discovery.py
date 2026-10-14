"""Freeze, test withheld bound discovery, and attempt the complete signed core.

No previous study is rerun. Parent obligations remain authoritative; this
capability study cannot pay a parent arithmetic leaf by benchmark success.
"""
import json
from pathlib import Path
import resource
import time

import multiscale_bound_discovery as P


ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'multiscale-bound-results/pilot-001'
PARENT = ROOT / 'core-moment-region-results/pilot-001'
PARENT_INPUT = ROOT / 'candidate10_moment_region_obligation.json'
ARCHIVE = ROOT / 'core-bound-results/pilot-001/checker_vectors.jsonl.gz'
ARCHIVE_REPORT = ROOT / 'core-bound-results/pilot-001/report.json'
SEED = 20261010
FILES = [
    'multiscale_bound_discovery.py', 'check_multiscale_bound_discovery.py',
    'multiscale_bound_sources.py', 'run_multiscale_bound_discovery.py',
    'test_multiscale_bound_discovery.py', 'test_check_multiscale_bound_discovery.py',
    'test_multiscale_bound_sources.py', 'multiscale_bound_discovery_protocol.txt',
    'BOUND_MECHANISM_SYNTHESIS_DESIGN_034.txt',
    'BOUND_DISCOVERY_CAPABILITY_REVIEW_034.txt',
    'multiscale_bound_discovery_development.json',
    'check_multiscale_bound_discovery_development.json',
    'multiscale_bound_sources_development.json',
]


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def read(path):
    return json.loads(path.read_text())


def parent_guard():
    if PARENT_INPUT.read_bytes() != (PARENT / 'publication-001/next_search_input.json').read_bytes():
        raise ValueError('current full obligation differs from accepted stage033')
    if not read(PARENT / 'verification.json')['verified']:
        raise ValueError('stage033 must retain accepted verification')
    if read(PARENT_INPUT)['whole_signed_bound_proved']:
        raise ValueError('this study addresses an unresolved parent target')
    source_report = read(ARCHIVE_REPORT)
    if (source_report['status'] != 'AUTOMATIC_CORE_BOUND_SEARCH_AND_INDEPENDENT_EVALUATION_COMPLETE'
            or source_report['checked_source_horizon'] != 262143
            or source_report['compared_vector_entries'] != 12 * 262144
            or source_report['all_source_crosses_and_units'] is not True):
        raise ValueError('complete previously verified arithmetic source archive required')


def freeze_guard():
    for name in FILES:
        if (ROOT / name).read_bytes() != (OUT / 'source_snapshot' / name).read_bytes():
            raise ValueError('changed frozen implementation: ' + name)
    if ARCHIVE.read_bytes() != (OUT / 'source_snapshot/core_vectors.jsonl.gz').read_bytes():
        raise ValueError('changed arithmetic source observations')
    if ARCHIVE_REPORT.read_bytes() != (OUT / 'source_snapshot/core_source_report.json').read_bytes():
        raise ValueError('changed source verification report')


def closure_callback(checker, model, meter):
    def check(states, transitions):
        result = checker.verify_closure(model, states, transitions, meter=meter)
        answer = dict(verified=result['valid'], audit=result)
        witness = result.get('counterexample')
        if witness is not None:
            answer['counterexample_n'] = witness['n']
        return answer
    return check


def main():
    import check_multiscale_bound_discovery as C
    import multiscale_bound_sources as S
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (16 * 1024 ** 3,
                        resource.getrlimit(resource.RLIMIT_AS)[1]))
    parent_guard()
    OUT.mkdir(parents=True, exist_ok=False)
    meter = P.Budget(dict(P.DEFAULT_SPEC, operation_cap=1000000000, seconds=1800))
    search_operations = 0
    try:
        for name in FILES:
            (OUT / 'source_snapshot' / name).parent.mkdir(parents=True, exist_ok=True)
            (OUT / 'source_snapshot' / name).write_bytes((ROOT / name).read_bytes())
        (OUT / 'source_snapshot/core_vectors.jsonl.gz').write_bytes(ARCHIVE.read_bytes())
        (OUT / 'source_snapshot/core_source_report.json').write_bytes(ARCHIVE_REPORT.read_bytes())
        write(OUT / 'protocol.json', dict(spec=P.DEFAULT_SPEC, seed=SEED,
            parent_input=str(PARENT_INPUT.relative_to(ROOT)),
            arithmetic_source=str(ARCHIVE.relative_to(ROOT)),
            source_files=FILES, arithmetic_horizon=262143, arithmetic_bases=[2, 3],
            expected_answers_available_to_generator=False,
            challenge_designer_knows_grammar=True, hashes=False,
            whole_signed_bound_proved=False, RH_proved=False))
        # Instances are created only after all implementation bytes are saved.
        challenges = S.create_challenges(OUT, SEED, meter=meter, frozen=True)
        write(OUT / 'challenge_index.json', challenges)
        results = []
        for entry in challenges:
            meter.charge()
            model = read(OUT / entry['model_file'])
            observe = S.model_source(model, meter=meter)
            oracle = closure_callback(C, model, meter)
            result = P.discover(observe, model['base'], closure_oracle=oracle)
            search_operations += result['operations']
            check = (C.verify(model, result['certificate'], meter=meter)
                     if result['status'] == 'certificate_proposed' else None)
            if check is not None and not check['verified']:
                raise ValueError('proposed benchmark bound not admitted')
            ablation = P.discover(observe, model['base'], P.no_state_expansion(), oracle)
            search_operations += ablation['operations']
            ablation_check = (C.verify(model, ablation['certificate'], meter=meter)
                              if ablation['status'] == 'certificate_proposed' else None)
            write(OUT / 'cases' / (entry['id'] + '.json'), dict(
                search=result, verification=check, ablation=ablation, ablation_verification=ablation_check))
            results.append(dict(id=entry['id'], status=result['status'],
                states=len(result['states']), source_queries=result['source_queries'],
                alpha=None if check is None else check['alpha'],
                verified=check is not None and check['verified'],
                ablation_status=ablation['status'],
                ablation_alpha=None if ablation_check is None else ablation_check['alpha'],
                counterexamples=sum(t['event'] in {'finite_counterexample', 'universal_closure_attempt'}
                    and (t['event'] == 'finite_counterexample' or not t['result']['verified'])
                    for t in result['trace'])))
            print(json.dumps(results[-1]), flush=True)
        # Expected labels are only opened after the independent proof attempts.
        truth = {entry['id']: read(OUT / entry['truth_file']) for entry in challenges}
        write(OUT / 'posthoc_challenge_truth.json', truth)
        print('Attempting multiscale closure for the complete archived signed arithmetic core.', flush=True)
        from flint import ctx
        ctx.prec = 192
        observe, source_info = S.load_complete_core(OUT / 'source_snapshot/core_vectors.jsonl.gz',
                                                    262143, meter=meter)
        write(OUT / 'arithmetic_source.json', source_info)
        core_results = []
        for base in (2, 3):
            spec = dict(P.DEFAULT_SPEC, max_source_index=262142)
            result = P.discover(observe, base, spec)
            search_operations += result['operations']
            # No source recurrence or arithmetic theorem is manufactured here.
            check = dict(verified=False, status='no_global_arithmetic_closure_certificate',
                         whole_signed_bound_proved=False, RH_proved=False)
            write(OUT / 'arithmetic' / ('base-' + str(base) + '.json'), dict(search=result, verification=check))
            core_results.append(dict(base=base, status=result['status'], states=len(result['states']),
                source_queries=result['source_queries'],
                unresolved_section=result.get('unresolved_section'), bound_proved=False))
            print(json.dumps(core_results[-1]), flush=True)
        freeze_guard()
        parent_guard()
        development = {name: read(ROOT / name) for name in FILES if name.endswith('_development.json')}
        report = dict(status='CAPABILITY_TEST_COMPLETE_ARITHMETIC_BOUND_OPEN',
            benchmark_results=results, arithmetic_results=core_results,
            verified_benchmark_bounds=sum(r['verified'] for r in results),
            verified_benchmark_sublinear_bounds=sum(r['verified'] and P.F(r['alpha']) < 1 for r in results),
            benchmark_is_evidence_of_RH_probability=False,
            benchmark_designer_knows_grammar=True,
            actual_arithmetic_globally_proved_relations=0,
            actual_arithmetic_new_bound_payments=0,
            current_joint_remainder_numerically_isolated=False,
            arithmetic_branch='direct complete core f; inherited Z033 and g=f-e unchanged',
            stage033_obligations_retained=True,
            new_arithmetic_validation_range=False,
            search_operations=search_operations, source_and_checker_operations=meter.operations,
            development_receipts=development, elapsed_seconds=time.monotonic() - started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            whole_signed_bound_proved=False, RH_proved=False)
        write(OUT / 'report.json', report)
        write(OUT / 'next_search_tasks.json', dict(
            authoritative_input=str(PARENT_INPUT.relative_to(ROOT)),
            unchanged_parent_status='moment_regions_verified_core_open',
            priority0='Find a globally justified arithmetic state law or more general bound construction for the complete signed core and joint remainder.',
            failed_finite_grammar='constant-matrix closure of finitely many fixed-base sections',
            possible_extensions=['parameter-dependent prime/cofactor states with full source identities',
                'counterexample-driven structural expansion beyond fixed-base sections',
                'signed product and nonlinear auxiliary state synthesis'],
            no_extension_is_a_proved_bound=True,
            grammar_stop_is_not_arithmetic_impossibility=True,
            whole_signed_bound_proved=False, RH_proved=False))
        print(json.dumps({k: v for k, v in report.items() if k != 'development_receipts'}), flush=True)
    except Exception as error:
        write(OUT / 'terminal_failure.json', dict(type=type(error).__name__, message=str(error),
              search_operations=search_operations, other_operations=meter.operations,
              whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()
