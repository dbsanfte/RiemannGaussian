"""Run, independently check and publish one immutable bound-search study."""
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

from prime_bank_candidates import Meter
import core_split_bound_search as P
import run_core_frame_bounds as PRIOR


ROOT = Path(__file__).resolve().parent
INPUT = 'candidate10_frame_bound_obligation.json'
PARENT = ROOT/'core-frame-bound-results/pilot-001'
OUT = ROOT/'core-split-bound-results/pilot-001'
PUBLIC_INPUT = 'candidate10_split_bound_obligation.json'
TESTS = ['test_core_split_bound_search', 'test_run_core_split_bound_search',
         'test_check_core_split_bound_search']
RECEIPTS = ['core_split_bound_development.json', 'core_split_bound_checker_development.json']
FILES = ['bound_split_search.py', 'core_split_bound_search.py', 'check_core_split_bound_search.py',
         'run_core_split_bound_search.py', 'core_split_bound_search_protocol.txt',
         'CORE_SPLIT_BOUND_RULE_REVIEW_016.txt', 'core_truncated_inverse.py',
         'prime_bank_candidates.py', INPUT]+[t+'.py' for t in TESTS]+RECEIPTS
CAP = 300000000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def verify():
    PRIOR.verify()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)


def validate_receipts(receipts):
    total = 0
    for receipt in receipts:
        runs = receipt['runs']
        if (not runs or runs[-1]['returncode'] != 0 or
                receipt['operations'] != sum(r['operations'] for r in runs)):
            raise ValueError('complete passed development receipt, with all failures retained')
        total += receipt['operations']
    return total


def require_current_input(root, parent):
    if (root/INPUT).read_bytes() != (parent/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('exact current published source obligation')
    if read(parent/'report.json')['status'] != 'FRAME_RECOVERY_BOUND_REDUCTIONS_AND_COMMON_MODE_OBSTRUCTION_VERIFIED':
        raise ValueError('verified inherited source and open common-mode obligation')


def main():
    import check_core_split_bound_search as CHECK
    started = time.monotonic()
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    PRIOR.verify()
    require_current_input(ROOT, PARENT)
    parent = read(ROOT/INPUT)
    development_ops = validate_receipts([read(ROOT/name) for name in RECEIPTS])
    if OUT.exists():
        raise FileExistsError('preserve every terminal study; no unchanged restart')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    write(OUT/'protocol.json', dict(schema='core-split-bound-run-v1', input=INPUT,
        spec=P.DEFAULT_SPEC, supplied_rule_review='CORE_SPLIT_BOUND_RULE_REVIEW_016.txt',
        purpose='machine search over splits, source applications and complete proof routes',
        generator_model_calls=0, actual_source_observations=0, numerical_candidate_scores=0,
        memory_limit_bytes=4*1024**3, test_memory_limit_bytes=2*1024**3,
        runtime_limit_seconds=1800, inclusive_operation_cap=CAP, hashes=False,
        general_analytic_prover=False, whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(CAP, 1800)
    meter.charge(2000000)
    tests_started = time.monotonic()
    script = ('import resource,runpy,sys; '
              'resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,resource.getrlimit(resource.RLIMIT_AS)[1])); '
              'sys.argv=["unittest"]+sys.argv[1:]; runpy.run_module("unittest",run_name="__main__")')
    tests = subprocess.run([sys.executable, '-B', '-c', script, *TESTS], cwd=ROOT,
                           capture_output=True, text=True, timeout=300)
    test_ops = sum(map(int, re.findall(r'operations=(\d+)', tests.stdout)))
    write(OUT/'frozen_tests.json', dict(returncode=tests.returncode, stdout=tests.stdout,
        stderr=tests.stderr, operations=test_ops, elapsed_seconds=time.monotonic()-tests_started))
    if tests.returncode:
        raise RuntimeError('frozen owned tests failed')
    result = P.search(parent, P.DEFAULT_SPEC, meter)
    checked = CHECK.verify_search(parent, result, meter)
    if not checked['verified']:
        raise ArithmeticError('independent source and bound certificate verification failed')
    result_file = str((OUT/'search.json').relative_to(ROOT))
    next_input = P.feedback(result, INPUT, result_file)
    feedback_check = CHECK.verify_feedback(result, next_input, INPUT, result_file, meter)
    if not feedback_check['verified']:
        raise ArithmeticError('independent open-obligation feedback verification failed')
    write(OUT/'search.json', result)
    write(OUT/'verification.json', dict(search=checked, feedback=feedback_check))
    write(OUT/'next_search_input.json', next_input)
    total = meter.operations+development_ops+test_ops
    if total > CAP:
        raise OverflowError('inclusive operation cap, including development and frozen tests')
    verify()
    chosen = result['geometries'][result['selected_geometry']]
    report = dict(status='SPLIT_AND_PROOF_ROUTE_COMPONENT_CONTROLS_VERIFIED_WITH_OPEN_SIGNED_CORE',
        **result['statistics'], selected_geometry=chosen['id'], alpha=chosen['alpha'], gamma=chosen['gamma'],
        generated_split_parameters={k: v['parameter'] for k, v in result['split_certificates'].items()},
        selected_controls=[dict(source_key=a['source_key'], rule=a['routes'][a['selected_route']]['rule'],
            energy=a['routes'][a['selected_route']]['energy'],
            target_constant=a['routes'][a['selected_route']]['target_constant'])
            for a in chosen['applications'] if a['component_target_proved']],
        arithmetic_source_observations=0, model_calls_in_search=0,
        main_operations=meter.operations, inclusive_operations=total,
        elapsed_seconds=time.monotonic()-started, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        complete_signed_bounds_proved=0, whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'report.json', report)
    publication = OUT/'publication-001'
    publication.mkdir()
    raw = (OUT/'next_search_input.json').read_bytes()
    for path in (publication/'next_search_input.json', ROOT/PUBLIC_INPUT):
        with path.open('xb') as stream:
            stream.write(raw)
    write(OUT.parent/'latest.json', dict(report=str((OUT/'report.json').relative_to(ROOT)),
        input=PUBLIC_INPUT, status=report['status'], whole_signed_bound_proved=False, RH_proved=False))
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json', dict(error_type=type(error).__name__, error=str(error),
                status='incomplete', whole_signed_bound_proved=False, RH_proved=False))
        raise
