"""Freeze and run one source-bound discovery/feedback experiment.

Old studies remain unchanged. The output is a capability/obstruction result,
not a replacement payment of the accepted complete signed-core obligation.
"""
import json
from pathlib import Path
import resource
import time

import prime_cofactor_discovery as P

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'prime-cofactor-bound-results/pilot-001'
PARENT = ROOT / 'candidate10_moment_region_obligation.json'
ACCEPTED = ROOT / 'core-moment-region-results/pilot-001/publication-001/next_search_input.json'
ARCHIVE = ROOT / 'core-bound-results/pilot-001/checker_vectors.jsonl.gz'
SOURCE_REPORT = ROOT / 'core-bound-results/pilot-001/report.json'
PRIOR_SNAPSHOT = ROOT / 'multiscale-bound-results/pilot-001/source_snapshot'
SCALES = (256, 1024, 4096, 16384, 65536)
FILES = [
    'prime_cofactor_discovery.py', 'check_prime_cofactor_discovery.py',
    'prime_cofactor_observations.py', 'run_prime_cofactor_discovery.py',
    'test_prime_cofactor_discovery.py', 'test_check_prime_cofactor_discovery.py',
    'test_prime_cofactor_observations.py', 'prime_cofactor_discovery_protocol.txt',
    'prime_cofactor_discovery_development.json',
    'check_prime_cofactor_discovery_development.json',
    'prime_cofactor_observations_development.json',
    'PRIME_COFACTOR_BOUND_RULE_REVIEW_035.txt', 'PRIME_COFACTOR_CHECK_SCOPE_035.txt',
]


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def read(path):
    return json.loads(path.read_text())


def parent_guard():
    if PARENT.read_bytes() != ACCEPTED.read_bytes():
        raise ValueError('accepted033 complete obligation changed')
    if not read(ROOT / 'core-moment-region-results/pilot-001/verification.json')['verified']:
        raise ValueError('accepted033 proof/check ancestry required')
    if read(PARENT)['whole_signed_bound_proved']:
        raise ValueError('experiment addresses the open complete source')
    report = read(SOURCE_REPORT)
    if (report['status'] != 'AUTOMATIC_CORE_BOUND_SEARCH_AND_INDEPENDENT_EVALUATION_COMPLETE'
            or report['checked_source_horizon'] != 262143
            or report['compared_vector_entries'] != 12*262144
            or report['all_source_crosses_and_units'] is not True):
        raise ValueError('complete independent arithmetic archive audit required')
    # Reuse the existing archive snapshot; no second88MB copy or digest.
    if ARCHIVE.read_bytes() != (PRIOR_SNAPSHOT / 'core_vectors.jsonl.gz').read_bytes():
        raise ValueError('previously verified archive bytes changed')
    if SOURCE_REPORT.read_bytes() != (PRIOR_SNAPSHOT / 'core_source_report.json').read_bytes():
        raise ValueError('previously verified archive audit changed')


def freeze_guard():
    for name in FILES:
        if (ROOT / name).read_bytes() != (OUT / 'source_snapshot' / name).read_bytes():
            raise ValueError('frozen035 source changed: '+name)


def main():
    import check_prime_cofactor_discovery as C
    import prime_cofactor_observations as O
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (16*1024**3,
                        resource.getrlimit(resource.RLIMIT_AS)[1]))
    parent_guard()
    OUT.mkdir(parents=True, exist_ok=False)
    try:
        for name in FILES:
            target = OUT / 'source_snapshot' / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / name).read_bytes())
        write(OUT / 'protocol.json', dict(symbolic_spec=P.SPEC, scales=SCALES,
            source_files=FILES, source_archive=str(ARCHIVE.relative_to(ROOT)),
            archive_byte_reference=str(PRIOR_SNAPSHOT.relative_to(ROOT) / 'core_vectors.jsonl.gz'),
            parent=str(PARENT.relative_to(ROOT)), earlier_source_knowledge=True,
            held_out_data=False, snapshot_precedes_actual_source_discovery=True,
            no_new_archive_copy=True, hashes=False,
            whole_signed_bound_proved=False, RH_proved=False))
        source = P.core_source()
        search = P.discover(source)
        write(OUT / 'search.json', search)
        if search['status'] != 'universal_law_proposed':
            raise ValueError('prime/cofactor module did not close within frozen grammar')
        meter = C.Meter()
        verification = C.verify(source, search['certificate'], meter=meter)
        if not verification['verified']:
            raise ValueError('independent source-law/bound verification failed')
        write(OUT / 'verification.json', verification)
        print(json.dumps(dict(event='universal_prime_states_verified',
            states=len(search['states']),
            root_frontier=search['certificate']['frontier_bounds'][0])), flush=True)
        joined = P.search_joined_forms(search['certificate']['frontier_bounds'][0])
        joined_check = C.verify_joined_forms(search['certificate']['frontier_bounds'][0],
                                            joined, meter=meter,
                                            source=source, states=search['states'])
        if not joined_check['verified']:
            raise ValueError('joined-storage classifications did not verify')
        write(OUT / 'joined_storage_search.json', joined)
        write(OUT / 'joined_storage_verification.json', joined_check)
        next_input = P.feedback(search, verification, joined)
        write(OUT / 'next_search_input.json', next_input)
        print(json.dumps(dict(event='joined_storage_search_verified',
                              counts=joined['counts'])), flush=True)
        observations = O.observe_archive(ARCHIVE, search['certificate'], scales=SCALES)
        if not observations['verified']:
            raise ValueError('finite arithmetic identity observations failed')
        write(OUT / 'arithmetic_observations.json', observations)
        freeze_guard()
        parent_guard()
        if time.monotonic()-started > 900:
            raise RuntimeError('complete stage035 runtime cap900seconds')
        receipts = {name: read(ROOT/name) for name in FILES if name.endswith('_development.json')}
        report = dict(status='PRIME_STATES_AND_AUXILIARY_BOUNDS_VERIFIED_JOINED_BOUND_OPEN',
            generated_state_count=len(search['states']),
            universal_all_prime_all_valuation_closure=True,
            exact_auxiliary_bound_count=len(search['certificate']['frontier_bounds']),
            core_rough_frontier=search['certificate']['frontier_bounds'][0],
            joined_storage_candidates=len(joined['rows']), joined_storage_counts=joined['counts'],
            observations_file='arithmetic_observations.json', actual_scales=SCALES,
            source_index_horizon=2*max(SCALES)-1, source_archive_horizon=262143,
            reused_arithmetic_data=True, current_joint_Z033_isolated=False,
            branch='direct complete original f; stage033 residual and all144 bindings unchanged',
            new_full_core_bound_payments=0, capability_is_not_RH_success_probability=True,
            search_operations=search['operations']+joined['operations'],
            checker_operations=meter.operations,
            observation_operations=observations['metadata']['operations'],
            development_receipts=receipts,
            elapsed_seconds=time.monotonic()-started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            whole_signed_bound_proved=False, RH_proved=False)
        write(OUT / 'report.json', report)
        print(json.dumps({k:v for k,v in report.items() if k not in
                         ('development_receipts', 'core_rough_frontier')}), flush=True)
    except Exception as error:
        write(OUT / 'terminal_failure.json', dict(error=type(error).__name__,
            message=str(error), elapsed_seconds=time.monotonic()-started,
            observation_counts=getattr(error, 'observation_counts', None),
            whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()
