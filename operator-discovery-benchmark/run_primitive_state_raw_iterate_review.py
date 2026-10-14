"""Archive a separate coordinate-export correction; no solver or refitting.

The frozen original trace is retained byte-for-byte. This review replays its
native x using its recorded bijective map and independently rebuilds the
original equations to evaluate that vector. The canonical matrix is not rebuilt.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import time
import check_primitive_state_raw_iterate as RAW
import check_primitive_state_solver_trace_run as CHECK

ROOT = Path(__file__).resolve().parent
RUN = ROOT / 'cancellation-arithmetic-results/primitive-state-solver-trace-001'
SOURCES = ['check_primitive_state_raw_iterate.py', 'run_primitive_state_raw_iterate_review.py',
           'test_check_primitive_state_raw_iterate.py']
INPUT_NAMES = ['receipt.json', 'independent_verification.json', 'protocol.json', 'source_seal.json',
               'jobs/primal-trace.json', 'jobs/primal.json']
FLAGS = dict(certified=False, exact_admission=False, infeasibility_proved=False,
             global_bound_proved=False, RH_proved=False)


def write(path, value):
    payload = json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + '\n'
    if len(payload.encode()) > 8 * 1024**2:
        raise OverflowError('review artifact byte cap')
    with path.open('x') as stream:
        stream.write(payload)


def bound_inputs():
    review = CHECK.read(RUN / 'independent_verification.json')
    if review.get('all_passed') is not True or review.get('mathematical_feasibility') != 'UNKNOWN':
        raise ValueError('completed original independent diagnostic review required')
    CHECK.scope(review, required=True)
    for name, h in review['input_sha256'].items():
        if CHECK.sha(CHECK.path_under(RUN, name)) != h:
            raise ValueError('bound original review input ' + name)
    protocol = CHECK.read(RUN / 'protocol.json'); CHECK.verify_protocol(protocol)
    receipt = CHECK.read(RUN / 'receipt.json'); CHECK.verify_inventory(RUN, receipt)
    source = CHECK.read(RUN / 'source_seal.json')
    for name, h in source.items():
        if CHECK.sha(CHECK.path_under(ROOT, name)) != h or CHECK.sha(CHECK.path_under(RUN / 'frozen_source', name)) != h:
            raise ValueError('immutable original source ' + name)
    return {str((RUN / name).relative_to(ROOT)): CHECK.sha(RUN / name) for name in INPUT_NAMES}


def review(directory):
    started = time.monotonic(); out = Path(directory).resolve()
    if out.exists():
        raise FileExistsError('exclusive native coordinate review')
    inputs = bound_inputs()
    sources = {name: CHECK.sha(ROOT / name) for name in SOURCES}
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', 'test_check_primitive_state_raw_iterate'],
                           cwd=ROOT, capture_output=True, text=True, timeout=180)
    test_record = dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr)
    if tests.returncode or 'Ran 7 tests' not in tests.stderr or not tests.stderr.rstrip().endswith('OK'):
        raise ValueError('coordinate replay calibration passed')
    out.mkdir(); (out / 'frozen_source').mkdir()
    for name in SOURCES:
        (out / 'frozen_source' / name).write_bytes((ROOT / name).read_bytes())
    write(out / 'tests.json', test_record)
    write(out / 'input.json', dict(input_sha256=inputs, source_sha256=sources, **FLAGS))
    trace = CHECK.read(RUN / 'jobs/primal-trace.json')
    coordinates = RAW.replay(trace)
    expected, geometry = CHECK.rebuild()
    metadata = CHECK.read(RUN / 'jobs/primal.json')
    CHECK.verify_metadata(metadata, 'primal', 1, expected)
    CHECK.verify_compilation(metadata, geometry)
    corrected = copy.deepcopy(trace)
    corrected['original_vector'] = coordinates['original_vector']
    corrected['diagnostics'] = {}
    corrected['vector_role'] = 'raw_failed_last_iterate'
    check = CHECK.complete_trace_check(RUN, 'primal', corrected, geometry,
                                     CHECK.read(RUN / 'protocol.json'), CHECK.read(RUN / 'source_seal.json'))
    if bound_inputs() != inputs or any(CHECK.sha(ROOT / name) != h or CHECK.sha(out / 'frozen_source' / name) != h for name, h in sources.items()):
        raise ValueError('source or input changed during coordinate review')
    report = dict(schema='primitive-state-native-coordinate-independent-review-v1', all_passed=True,
        source_sha256=sources, input_sha256=inputs, tests_passed=7,
        coordinate_replay=coordinates, corrected_original_equation_check=check,
        original_system_hash=trace['original_system_hash'],
        exact_equation_source_hash=trace['transformation_receipt']['original_hash'],
        original_trace_sha256=CHECK.sha(RUN / 'jobs/primal-trace.json'),
        native_termination_status=trace['termination_status'],
        full_arithmetic_rebuilds=1, geometry_rebuilds=1,
        scalar_projection_was_applied_to_archived_vector=True,
        canonical_matrix_independently_rebuilt=False,
        canonical_variable_map_independently_derived=False,
        original_trace_modified=False, solver_rerun=False, refitted=False,
        numerical_diagnostics_only=True, mathematical_feasibility='UNKNOWN',
        elapsed_seconds=time.monotonic() - started, **FLAGS)
    write(out / 'report.json', report)
    files = {str(p.relative_to(out)): CHECK.sha(p) for p in sorted(out.rglob('*')) if p.is_file()}
    write(out / 'seal.json', dict(schema=1, files_sha256=files, **FLAGS))
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('directory')
    args = parser.parse_args(); r = review(args.directory)
    print(json.dumps(dict(all_passed=r['all_passed'], changed_coordinates=r['coordinate_replay']['changed_coordinate_count'],
        corrected_original_equation_diagnostics=r['corrected_original_equation_check']['diagnostics'], **FLAGS), sort_keys=True))
