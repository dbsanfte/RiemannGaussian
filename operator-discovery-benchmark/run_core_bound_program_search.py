"""One bounded, immutable search of actual-core bound programs."""
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
from flint import arb, ctx
from prime_bank_candidates import Meter
import core_bound_program_search as P
import check_core_bound_program_search as C
import check_core_prime_transport as T
from run_core_prime_transport import verify as verify_parent


ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'core-prime-transport-results/pilot-001'
INPUT = 'candidate10_transport_control_obligation.json'
OUT = ROOT/'core-bound-program-results/pilot-001'
TEST = 'test_core_bound_program_search'
RECEIPT = 'core_bound_program_search_development.json'
FILES = ['core_bound_program_search.py', 'check_core_bound_program_search.py',
         'run_core_bound_program_search.py', 'core_bound_program_search_protocol.txt',
         TEST+'.py', RECEIPT, 'CORE_BOUND_PROGRAM_SEARCH_REVIEW_014.txt',
         'CORE_SELECTED_GROUPING_REVIEW_010.txt', 'CORE_PRIME_COMPOSITE_TRANSPORT_REVIEW_011.txt',
         'check_core_prime_transport.py', 'prime_bank_candidates.py', INPUT]
CAP = 300000000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write('\n')


def verify():
    verify_parent()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)


def main():
    start = time.monotonic()
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    ctx.prec = 192
    verify_parent()
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('current published parent input')
    prior = read(ROOT/INPUT)
    if prior['whole_signed_bound_proved'] or prior['RH_proved']:
        raise ValueError('expected unresolved core goal')
    parents = [o for o in prior['generated_bound_obligations'] if o['storage_program']['auxiliary'] is None]
    if not parents or any(o['uniform_premise_established'] for o in parents):
        raise ValueError('all unresolved baseline core inputs')
    goals = {Q(o['shape']['log_power'])+int(Q(o['shape']['rho']) == 1) for o in parents}
    # Preserve the parent's requested degree and one weaker fixed-polylog
    # target, also sufficient for the retained all-epsilon energy goal.
    target_degrees = sorted(goals | {p+1 for p in goals})
    spec = dict(degree=3, coefficient_cap=3, coefficient_l1=8,
                recovery_multipliers=['-1', '1'],
                gains=['0', '1/6', '1/3', '1/2', '2/3', '5/6', '1', '3/2', '2'],
                meshes=['1/3', '1/2', '2/3'],
                target_log_powers=list(map(str, target_degrees)), rhos=['1/2', '1'], archive_limit=36)
    development = read(ROOT/RECEIPT)
    if development['runs'][-1]['returncode'] or development['operations'] != sum(r['operations'] for r in development['runs']):
        raise ValueError('complete passed owned development receipt')
    if OUT.exists():
        raise FileExistsError('one terminal search; do not overwrite or replay unchanged')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    write(OUT/'protocol.json', dict(schema='target-driven-bound-program-search-v1', grammar=spec,
        input=INPUT, selected_parent_ids=[o['id'] for o in parents],
        other_parent_obligations_retained=True,
        analyst_supplied=['logarithmic prefix feature grammar', 'divisor envelope',
                         'product-rule and projection inequalities', 'recovery and dyadic induction rules'],
        detector_generated=['polynomial combinations', 'exact recovery coefficients', 'fractional log reserves',
                            'uniform detail constants', 'backward exponent budgets',
                            'specific signed arithmetic kernel obligations', 'fair bounded archive'],
        selection='lowest recovery cost and description length within distinct geometry/target/recurrence/cancellation/gain cells; round-robin lanes',
        no_expected_candidate_formula_in_selector=True, source_values_used_for_selection=False,
        source_generation=False, new_source_observations=0, source_horizon_already_observed=524287,
        workflow='detector generates and checks rule compositions; independent analysts audit rules or tackle emitted signed leaves',
        supported_proof_search='finite supplied rule library; no autonomous invention of arbitrary analytic theorems',
        previous_projection_pilot='terminal serialization failure; none of its numerical outputs certify this run',
        memory_limit_bytes=4*1024**3, operations_cap=CAP, runtime_seconds=900, hashes=False))
    meter = Meter(CAP, 900)
    meter.charge(1000000)
    test_start = time.monotonic()
    test = subprocess.run([sys.executable, '-B', '-m', 'unittest', TEST], cwd=ROOT, capture_output=True, text=True)
    test_ops = sum(map(int, re.findall(r'operations=(\d+)', test.stdout)))
    write(OUT/'frozen_tests.json', dict(returncode=test.returncode, stdout=test.stdout, stderr=test.stderr,
        operations=test_ops, elapsed_seconds=time.monotonic()-test_start))
    if test.returncode:
        raise RuntimeError('frozen checks failed')
    source = read(PARENT/'source_program.json')
    z = (arb(2)/3).zeta()
    Ru = arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z)
    binding = []
    for parent in parents:
        checked = T.verify_recovery(parent['transport_program'], source, Ru, meter)
        if not checked['verified'] or not checked['cofinal_recovery']:
            raise ValueError('actual full source and paid transport required')
        binding.append(dict(parent_obligation=parent['id'], checked=checked))
    meter.charge(1000)
    write(OUT/'source_binding.json', dict(complete_source=source, residue=str(Ru), coefficient_constant='37/2',
        proof='complete local modes obey |nu0|<=d2 and the other three <=d2; 3beta+Ru<37/2; transport preserves |g|<=|f| pointwise',
        reviewed_in=['CORE_SELECTED_GROUPING_REVIEW_010.txt', 'CORE_PRIME_COMPOSITE_TRANSPORT_REVIEW_011.txt'],
        bound_inputs=binding, source_coefficients_evaluated=0))
    result = P.search(spec, meter)
    for program in result['programs']:
        C.check_program(program, meter)
    for branch in result['branches']:
        C.check_branch(result['programs'][branch['program_id']], branch, meter)
    write(OUT/'programs.json', result['programs'])
    write(OUT/'branches.json', result['branches'])
    write(OUT/'polynomials.json', result['polynomials'])
    write(OUT/'selection.json', result['selected'])
    obligations = []
    for branch in result['selected']:
        program = result['programs'][branch['program_id']]
        for parent in parents:
            ob = P.open_obligation(program, branch, parent)
            ob['id'] = 'bound_'+str(branch['id'])+'_source_'+str(parent['finite_verification']['transport_id'])
            ob['source_majorant_verified'] = True
            ob['weak_fact_obstruction'] = P.weak_fact_guard(program, branch)
            C.check_dependency_graph(ob)
            obligations.append(ob)
    next_input = dict(schema='detector-bound-program-search-input-v1', status='open',
        parent_obligation=prior, generated_bound_program_obligations=obligations,
        next_priority='Search identities/controls for the complete signed source-pair kernel emitted in each required coarse increment; generic divisor envelopes cannot close it',
        automatic_feedback=['unpaid positive powers retained with rejection reason',
            'log gains ranked only after recovery costs',
            'original fixed-C recurrence is not discharged by a different conditional recurrence',
            'same weak-fact proof path rejected by composite countermodel',
            'all-scale leaves remain open until proved independently'],
        detector_generates_bound_constructions=True, detector_proves_supported_local_controls=True,
        detector_has_general_analytic_prover=False,
        all_scale_signed_control_proved=False, whole_signed_bound_proved=False, RH_proved=False,
        original_target_and_corrections_retained=True, new_source_observations=0)
    write(OUT/'next_search_input.json', next_input)
    total = meter.operations+development['operations']+test_ops
    if total > CAP:
        raise OverflowError('inclusive operation cap')
    verify()
    report = dict(status='BOUND_PROGRAM_SEARCH_VERIFIED_WITH_OPEN_SIGNED_LEAVES',
        polynomial_count=len(result['polynomials']), recovery_constructions=result['constructions'],
        generated_bound_programs=len(result['programs']), target_branches=len(result['branches']),
        branch_statuses=dict(Counter(b['status'] for b in result['branches'])),
        selected_constructions=len(result['selected']), bound_source_inputs=len(parents),
        generated_signed_obligations=len(obligations), all_scale_signed_bounds_proved=0,
        generated_cancellation_orders=dict(Counter(p['cancellation_order'] for p in result['programs'])),
        source_values_used_for_selection=False, model_calls_in_search=0,
        main_operations=meter.operations, inclusive_operations=total,
        elapsed_seconds=time.monotonic()-start, peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        previous_projection_numerical_verification_complete=False,
        whole_signed_bound_proved=False, RH_proved=False, new_source_observations=0)
    write(OUT/'report.json', report)
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'report.json').exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__,
                error=str(error), whole_signed_bound_proved=False, RH_proved=False))
        raise
